import Mettapedia.GSLT.LanguageDef.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.ReflectiveSupportRenaming
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Structural transport of selected pattern occurrences

The term transformations used by generated languages preserve the recursive
shape of `Pattern` while changing selected leaf or constructor labels.  This
module packages that common traversal and proves the corresponding exact
action on one-hole contexts.

The reflection theorem is deliberately existential.  A structural action may
identify two different free-variable names or constructor labels, so a target
occurrence has a source position but need not have a unique source spelling.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A state-indexed, shape-preserving action on patterns.

The state records transformations such as the current locally nameless binder
depth.  Every recursive child receives the state appropriate to its syntactic
position; labels and leaf names may be non-injectively renamed. -/
structure StructuralPatternAction (State : Type) where
  mapBVar : State → Nat → Nat
  mapFVar : State → String → String
  mapConstructor : State → String → String
  underLambda : State → State
  underMultiLambda : State → Nat → State
  underSubstBody : State → State
  underSubstReplacement : State → State

namespace StructuralPatternAction

/-- Apply a structural action to a pattern at the supplied state. -/
def map {State : Type} (action : StructuralPatternAction State) :
    State → Pattern → Pattern
  | state, .bvar index => .bvar (action.mapBVar state index)
  | state, .fvar name => .fvar (action.mapFVar state name)
  | state, .apply constructor arguments =>
      .apply (action.mapConstructor state constructor)
        (arguments.map (action.map state))
  | state, .lambda binder body =>
      .lambda binder (action.map (action.underLambda state) body)
  | state, .multiLambda arity binders body =>
      .multiLambda arity binders
        (action.map (action.underMultiLambda state arity) body)
  | state, .subst body replacement =>
      .subst (action.map (action.underSubstBody state) body)
        (action.map (action.underSubstReplacement state) replacement)
  | state, .collection collectionType elements rest =>
      .collection collectionType (elements.map (action.map state)) rest
termination_by _ pattern => sizeOf pattern

/-- Apply a structural action to the fixed syntax of a one-hole context and
return the state at its hole. -/
def mapContext {State : Type} (action : StructuralPatternAction State) :
    State → OneHoleContext → OneHoleContext × State
  | state, .hole => (.hole, state)
  | state, .apply constructor before inner after =>
      let mapped := action.mapContext state inner
      (.apply (action.mapConstructor state constructor)
          (before.map (action.map state)) mapped.1
          (after.map (action.map state)),
        mapped.2)
  | state, .lambda binder inner =>
      let mapped := action.mapContext (action.underLambda state) inner
      (.lambda binder mapped.1, mapped.2)
  | state, .multiLambda arity binders inner =>
      let mapped := action.mapContext
        (action.underMultiLambda state arity) inner
      (.multiLambda arity binders mapped.1, mapped.2)
  | state, .substBody inner replacement =>
      let mapped := action.mapContext (action.underSubstBody state) inner
      (.substBody mapped.1
          (action.map (action.underSubstReplacement state) replacement),
        mapped.2)
  | state, .substReplacement body inner =>
      let mapped := action.mapContext
        (action.underSubstReplacement state) inner
      (.substReplacement
          (action.map (action.underSubstBody state) body) mapped.1,
        mapped.2)
  | state, .collection collectionType before inner after rest =>
      let mapped := action.mapContext state inner
      (.collection collectionType (before.map (action.map state)) mapped.1
          (after.map (action.map state)) rest,
        mapped.2)

/-- Structural pattern transport commutes with filling its transported
one-hole context, including the exact state computed at the hole. -/
theorem map_fill {State : Type} (action : StructuralPatternAction State)
    (state : State) (context : OneHoleContext) (pattern : Pattern) :
    action.map state (context.fill pattern) =
      let mapped := action.mapContext state context
      mapped.1.fill (action.map mapped.2 pattern) := by
  induction context generalizing state with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, List.map_append,
        List.map_cons, inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [OneHoleContext.fill, map, mapContext, List.map_append,
        List.map_cons, inductionHypothesis]

/-- Invert a split of a mapped list while retaining the exact source prefix,
selected element, and suffix. -/
theorem exists_source_split_of_map_eq
    {Source Target : Type} (mapping : Source → Target) :
    ∀ (before : List Target) (sources : List Source)
      (middle : Target) (after : List Target),
      sources.map mapping = before ++ middle :: after →
      ∃ sourceBefore sourceMiddle sourceAfter,
        sources = sourceBefore ++ sourceMiddle :: sourceAfter ∧
        sourceBefore.map mapping = before ∧
        mapping sourceMiddle = middle ∧
        sourceAfter.map mapping = after
  | [], [], middle, after, equality => by
      simp at equality
  | [], source :: sources, middle, after, equality => by
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at equality
      exact ⟨[], source, sources, rfl, rfl, equality.1, equality.2⟩
  | target :: before, [], middle, after, equality => by
      simp at equality
  | target :: before, source :: sources, middle, after, equality => by
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at equality
      obtain ⟨sourceBefore, sourceMiddle, sourceAfter, sourcesEquality,
          beforeEquality, middleEquality, afterEquality⟩ :=
        exists_source_split_of_map_eq mapping before sources middle after
          equality.2
      refine ⟨source :: sourceBefore, sourceMiddle, sourceAfter, ?_, ?_,
        middleEquality, afterEquality⟩
      · simp [sourcesEquality]
      · simp [equality.1, beforeEquality]

/-- Reflect one filled target context through a structural action.  The
source occurrence and the state at its hole are constructed by following the
target zipper; no injectivity of any renaming component is required. -/
theorem exists_preimage_fill {State : Type}
    (action : StructuralPatternAction State) :
    ∀ (state : State) (targetContext : OneHoleContext)
      (sourceRoot targetPayload : Pattern),
      action.map state sourceRoot = targetContext.fill targetPayload →
      ∃ sourceContext sourcePayload holeState,
        sourceRoot = sourceContext.fill sourcePayload ∧
        action.mapContext state sourceContext = (targetContext, holeState) ∧
        action.map holeState sourcePayload = targetPayload
  | state, .hole, sourceRoot, targetPayload, equality => by
      exact ⟨.hole, sourceRoot, state, rfl, rfl, equality⟩
  | state, .apply targetConstructor before inner after, sourceRoot,
      targetPayload, equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | lambda binder body => simp [map, OneHoleContext.fill] at equality
      | multiLambda arity binders body =>
          simp [map, OneHoleContext.fill] at equality
      | subst body replacement => simp [map, OneHoleContext.fill] at equality
      | collection collectionType elements rest =>
          simp [map, OneHoleContext.fill] at equality
      | apply sourceConstructor sourceArguments =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨constructorEquality, argumentsEquality⟩ :=
            Pattern.apply.inj equality
          obtain ⟨sourceBefore, sourceMiddle, sourceAfter, sourceSplit,
              beforeEquality, middleEquality, afterEquality⟩ :=
            exists_source_split_of_map_eq (action.map state) before
              sourceArguments (inner.fill targetPayload) after
              argumentsEquality
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action state inner sourceMiddle targetPayload
              middleEquality
          refine ⟨.apply sourceConstructor sourceBefore sourceInner
              sourceAfter, sourcePayload, holeState, ?_, ?_, payloadEquality⟩
          · simp [OneHoleContext.fill, sourceSplit, sourceFill]
          · simp [mapContext, constructorEquality, beforeEquality,
              afterEquality, contextEquality]
  | state, .lambda targetBinder inner, sourceRoot, targetPayload,
      equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | apply constructor arguments =>
          simp [map, OneHoleContext.fill] at equality
      | multiLambda arity binders body =>
          simp [map, OneHoleContext.fill] at equality
      | subst body replacement => simp [map, OneHoleContext.fill] at equality
      | collection collectionType elements rest =>
          simp [map, OneHoleContext.fill] at equality
      | lambda sourceBinder sourceBody =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨binderEquality, bodyEquality⟩ := Pattern.lambda.inj equality
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action (action.underLambda state) inner
              sourceBody targetPayload bodyEquality
          refine ⟨.lambda sourceBinder sourceInner, sourcePayload, holeState,
            ?_, ?_, payloadEquality⟩
          · simp [OneHoleContext.fill, sourceFill]
          · simp [mapContext, binderEquality, contextEquality]
  | state, .multiLambda targetArity targetBinders inner, sourceRoot,
      targetPayload, equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | apply constructor arguments =>
          simp [map, OneHoleContext.fill] at equality
      | lambda binder body => simp [map, OneHoleContext.fill] at equality
      | subst body replacement => simp [map, OneHoleContext.fill] at equality
      | collection collectionType elements rest =>
          simp [map, OneHoleContext.fill] at equality
      | multiLambda sourceArity sourceBinders sourceBody =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨arityEquality, bindersEquality, bodyEquality⟩ :=
            Pattern.multiLambda.inj equality
          subst targetArity
          subst targetBinders
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action
              (action.underMultiLambda state sourceArity) inner sourceBody
              targetPayload bodyEquality
          refine ⟨.multiLambda sourceArity sourceBinders sourceInner,
            sourcePayload, holeState, ?_, ?_, payloadEquality⟩
          · simp [OneHoleContext.fill, sourceFill]
          · simp [mapContext, contextEquality]
  | state, .substBody inner targetReplacement, sourceRoot, targetPayload,
      equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | apply constructor arguments =>
          simp [map, OneHoleContext.fill] at equality
      | lambda binder body => simp [map, OneHoleContext.fill] at equality
      | multiLambda arity binders body =>
          simp [map, OneHoleContext.fill] at equality
      | collection collectionType elements rest =>
          simp [map, OneHoleContext.fill] at equality
      | subst sourceBody sourceReplacement =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨bodyEquality, replacementEquality⟩ :=
            Pattern.subst.inj equality
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action (action.underSubstBody state) inner
              sourceBody targetPayload bodyEquality
          refine ⟨.substBody sourceInner sourceReplacement, sourcePayload,
            holeState, ?_, ?_, payloadEquality⟩
          · simp [OneHoleContext.fill, sourceFill]
          · simp [mapContext, replacementEquality, contextEquality]
  | state, .substReplacement targetBody inner, sourceRoot, targetPayload,
      equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | apply constructor arguments =>
          simp [map, OneHoleContext.fill] at equality
      | lambda binder body => simp [map, OneHoleContext.fill] at equality
      | multiLambda arity binders body =>
          simp [map, OneHoleContext.fill] at equality
      | collection collectionType elements rest =>
          simp [map, OneHoleContext.fill] at equality
      | subst sourceBody sourceReplacement =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨bodyEquality, replacementEquality⟩ :=
            Pattern.subst.inj equality
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action
              (action.underSubstReplacement state) inner sourceReplacement
              targetPayload replacementEquality
          refine ⟨.substReplacement sourceBody sourceInner, sourcePayload,
            holeState, ?_, ?_, payloadEquality⟩
          · simp [OneHoleContext.fill, sourceFill]
          · simp [mapContext, bodyEquality, contextEquality]
  | state, .collection targetCollection before inner after targetRest,
      sourceRoot, targetPayload, equality => by
      cases sourceRoot with
      | bvar index => simp [map, OneHoleContext.fill] at equality
      | fvar name => simp [map, OneHoleContext.fill] at equality
      | apply constructor arguments =>
          simp [map, OneHoleContext.fill] at equality
      | lambda binder body => simp [map, OneHoleContext.fill] at equality
      | multiLambda arity binders body =>
          simp [map, OneHoleContext.fill] at equality
      | subst body replacement => simp [map, OneHoleContext.fill] at equality
      | collection sourceCollection sourceElements sourceRest =>
          simp only [map, OneHoleContext.fill] at equality
          obtain ⟨collectionEquality, elementsEquality, restEquality⟩ :=
            Pattern.collection.inj equality
          obtain ⟨sourceBefore, sourceMiddle, sourceAfter, sourceSplit,
              beforeEquality, middleEquality, afterEquality⟩ :=
            exists_source_split_of_map_eq (action.map state) before
              sourceElements (inner.fill targetPayload) after elementsEquality
          obtain ⟨sourceInner, sourcePayload, holeState, sourceFill,
              contextEquality, payloadEquality⟩ :=
            exists_preimage_fill action state inner sourceMiddle targetPayload
              middleEquality
          refine ⟨.collection sourceCollection sourceBefore sourceInner
              sourceAfter sourceRest, sourcePayload, holeState, ?_, ?_,
            payloadEquality⟩
          · simp [OneHoleContext.fill, sourceSplit, sourceFill]
          · simp [mapContext, collectionEquality, beforeEquality,
              afterEquality, restEquality, contextEquality]
termination_by _ targetContext _ _ => sizeOf targetContext

/-- Reflect an exact target occurrence through a structural action. -/
theorem exists_preimage_selection {State : Type}
    (action : StructuralPatternAction State) (state : State)
    {sourceRoot targetPayload : Pattern} {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (action.map state sourceRoot)) :
    ∃ sourcePayload sourceContext holeState,
      Selects sourcePayload sourceContext sourceRoot ∧
      action.mapContext state sourceContext = (targetContext, holeState) ∧
      action.map holeState sourcePayload = targetPayload := by
  obtain ⟨sourceContext, sourcePayload, holeState, sourceFill,
      contextEquality, payloadEquality⟩ :=
    action.exists_preimage_fill state targetContext sourceRoot targetPayload
      selected.fill_eq.symm
  refine ⟨sourcePayload, sourceContext, holeState, ?_, contextEquality,
    payloadEquality⟩
  rw [sourceFill]
  exact Selects.of_fill sourceContext sourcePayload

/-- Transport an exact source occurrence through a structural action. -/
def mapSelection {State : Type} (action : StructuralPatternAction State)
    (state : State) {sourcePayload sourceRoot : Pattern}
    {sourceContext : OneHoleContext}
    (selected : Selects sourcePayload sourceContext sourceRoot) :
    let mapped := action.mapContext state sourceContext
    Selects (action.map mapped.2 sourcePayload) mapped.1
      (action.map state sourceRoot) := by
  let mapped := action.mapContext state sourceContext
  have filled : mapped.1.fill (action.map mapped.2 sourcePayload) =
      action.map state sourceRoot := by
    rw [← selected.fill_eq]
    exact (action.map_fill state sourceContext sourcePayload).symm
  rw [← filled]
  exact Selects.of_fill mapped.1 (action.map mapped.2 sourcePayload)

/-! ## Existing structural transformations as actions -/

/-- Presentation-symbol mapping as a structural action. -/
def presentation (symbols : PresentationSymbols) :
    StructuralPatternAction Unit where
  mapBVar _ index := index
  mapFVar _ name := name
  mapConstructor _ constructor := symbols.constructor constructor
  underLambda := id
  underMultiLambda state _ := state
  underSubstBody := id
  underSubstReplacement := id

@[simp] theorem presentation_mapBVar (symbols : PresentationSymbols)
    (index : Nat) : (presentation symbols).mapBVar () index = index := rfl

@[simp] theorem presentation_mapFVar (symbols : PresentationSymbols)
    (name : String) : (presentation symbols).mapFVar () name = name := rfl

@[simp] theorem presentation_mapConstructor (symbols : PresentationSymbols)
    (constructor : String) :
    (presentation symbols).mapConstructor () constructor =
      symbols.constructor constructor := rfl

@[simp] theorem presentation_underLambda (symbols : PresentationSymbols) :
    (presentation symbols).underLambda () = () := rfl

@[simp] theorem presentation_underMultiLambda
    (symbols : PresentationSymbols) (arity : Nat) :
    (presentation symbols).underMultiLambda () arity = () := rfl

@[simp] theorem presentation_underSubstBody (symbols : PresentationSymbols) :
    (presentation symbols).underSubstBody () = () := rfl

@[simp] theorem presentation_underSubstReplacement
    (symbols : PresentationSymbols) :
    (presentation symbols).underSubstReplacement () = () := rfl

@[simp]
theorem presentation_map (symbols : PresentationSymbols) (pattern : Pattern) :
    (presentation symbols).map () pattern = mapPattern symbols pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [map, mapPattern, presentation_mapBVar]
  | hfvar name => simp only [map, mapPattern, presentation_mapFVar]
  | happly constructor arguments inductionHypothesis =>
      simp only [map, mapPattern, mapPatternList_eq_map,
        presentation_mapConstructor, Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simpa only [map, mapPattern, presentation_underLambda,
        Pattern.lambda.injEq, true_and] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [map, mapPattern, presentation_underMultiLambda,
        Pattern.multiLambda.injEq, true_and] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [map, mapPattern, presentation_underSubstBody,
        presentation_underSubstReplacement, Pattern.subst.injEq] using
        And.intro bodyInduction replacementInduction
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [map, mapPattern, mapPatternList_eq_map,
        Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left inductionHypothesis

@[simp]
theorem presentation_mapContext (symbols : PresentationSymbols)
    (context : OneHoleContext) :
    (presentation symbols).mapContext () context =
      (CIGSLT.mapOneHoleContext symbols context, ()) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      have beforeEquality :
          before.map ((presentation symbols).map ()) =
            before.map (mapPattern symbols) :=
        List.map_congr_left fun pattern _ => presentation_map symbols pattern
      have afterEquality :
          after.map ((presentation symbols).map ()) =
            after.map (mapPattern symbols) :=
        List.map_congr_left fun pattern _ => presentation_map symbols pattern
      simp only [mapContext, CIGSLT.mapOneHoleContext,
        presentation_mapConstructor, inductionHypothesis, beforeEquality,
        afterEquality]
  | lambda binder inner inductionHypothesis =>
      simp only [mapContext, CIGSLT.mapOneHoleContext,
        presentation_underLambda, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [mapContext, CIGSLT.mapOneHoleContext,
        presentation_underMultiLambda, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [mapContext, CIGSLT.mapOneHoleContext,
        presentation_underSubstBody, presentation_underSubstReplacement,
        presentation_map, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [mapContext, CIGSLT.mapOneHoleContext,
        presentation_underSubstBody, presentation_underSubstReplacement,
        presentation_map, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      have beforeEquality :
          before.map ((presentation symbols).map ()) =
            before.map (mapPattern symbols) :=
        List.map_congr_left fun pattern _ => presentation_map symbols pattern
      have afterEquality :
          after.map ((presentation symbols).map ()) =
            after.map (mapPattern symbols) :=
        List.map_congr_left fun pattern _ => presentation_map symbols pattern
      simp only [mapContext, CIGSLT.mapOneHoleContext, inductionHypothesis,
        beforeEquality, afterEquality]

/-- Ambient locally nameless renaming as a depth-indexed structural action. -/
def ambientBVarRenaming (rename : Nat → Nat) :
    StructuralPatternAction Nat where
  mapBVar depth index :=
    if index < depth then index else depth + rename (index - depth)
  mapFVar _ name := name
  mapConstructor _ constructor := constructor
  underLambda depth := depth + 1
  underMultiLambda depth arity := depth + arity
  underSubstBody depth := depth + 1
  underSubstReplacement := id

@[simp] theorem ambientBVarRenaming_mapBVar (rename : Nat → Nat)
    (depth index : Nat) :
    (ambientBVarRenaming rename).mapBVar depth index =
      if index < depth then index else depth + rename (index - depth) := rfl

@[simp] theorem ambientBVarRenaming_mapFVar (rename : Nat → Nat)
    (depth : Nat) (name : String) :
    (ambientBVarRenaming rename).mapFVar depth name = name := rfl

@[simp] theorem ambientBVarRenaming_mapConstructor (rename : Nat → Nat)
    (depth : Nat) (constructor : String) :
    (ambientBVarRenaming rename).mapConstructor depth constructor =
      constructor := rfl

@[simp] theorem ambientBVarRenaming_underLambda (rename : Nat → Nat)
    (depth : Nat) :
    (ambientBVarRenaming rename).underLambda depth = depth + 1 := rfl

@[simp] theorem ambientBVarRenaming_underMultiLambda (rename : Nat → Nat)
    (depth arity : Nat) :
    (ambientBVarRenaming rename).underMultiLambda depth arity =
      depth + arity := rfl

@[simp] theorem ambientBVarRenaming_underSubstBody (rename : Nat → Nat)
    (depth : Nat) :
    (ambientBVarRenaming rename).underSubstBody depth = depth + 1 := rfl

@[simp] theorem ambientBVarRenaming_underSubstReplacement
    (rename : Nat → Nat) (depth : Nat) :
    (ambientBVarRenaming rename).underSubstReplacement depth = depth := rfl

@[simp]
theorem ambientBVarRenaming_map (rename : Nat → Nat) (depth : Nat)
    (pattern : Pattern) :
    (ambientBVarRenaming rename).map depth pattern =
      ContextSubstitution.renameAmbientBVarsAt rename depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases inside : index < depth <;>
        simp [map, ContextSubstitution.renameAmbientBVarsAt,
          ambientBVarRenaming_mapBVar, inside]
  | hfvar name =>
      simp only [map, ContextSubstitution.renameAmbientBVarsAt,
        ambientBVarRenaming_mapFVar]
  | happly constructor arguments inductionHypothesis =>
      simp only [map, ContextSubstitution.renameAmbientBVarsAt,
        ambientBVarRenaming_mapConstructor, Pattern.apply.injEq, true_and]
      exact List.map_congr_left fun argument membership =>
        inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simpa only [map, ContextSubstitution.renameAmbientBVarsAt,
        ambientBVarRenaming_underLambda, Pattern.lambda.injEq, true_and] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [map, ContextSubstitution.renameAmbientBVarsAt,
        ambientBVarRenaming_underMultiLambda, Pattern.multiLambda.injEq,
        true_and] using inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [map, ContextSubstitution.renameAmbientBVarsAt,
        ambientBVarRenaming_underSubstBody,
        ambientBVarRenaming_underSubstReplacement, Pattern.subst.injEq] using
        And.intro (bodyInduction (depth + 1)) (replacementInduction depth)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [map, ContextSubstitution.renameAmbientBVarsAt,
        Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left fun element membership =>
        inductionHypothesis element membership depth

@[simp]
theorem ambientBVarRenaming_mapContext (rename : Nat → Nat) (depth : Nat)
    (context : OneHoleContext) :
    (ambientBVarRenaming rename).mapContext depth context =
      ContextSubstitution.renameAmbientContextAt rename depth context := by
  induction context generalizing depth with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      have beforeEquality :
          before.map ((ambientBVarRenaming rename).map depth) =
            before.map
              (ContextSubstitution.renameAmbientBVarsAt rename depth) :=
        List.map_congr_left fun pattern _ =>
          ambientBVarRenaming_map rename depth pattern
      have afterEquality :
          after.map ((ambientBVarRenaming rename).map depth) =
            after.map
              (ContextSubstitution.renameAmbientBVarsAt rename depth) :=
        List.map_congr_left fun pattern _ =>
          ambientBVarRenaming_map rename depth pattern
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        ambientBVarRenaming_mapConstructor, inductionHypothesis,
        beforeEquality, afterEquality]
  | lambda binder inner inductionHypothesis =>
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        ambientBVarRenaming_underLambda, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        ambientBVarRenaming_underMultiLambda, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        ambientBVarRenaming_underSubstBody,
        ambientBVarRenaming_underSubstReplacement,
        ambientBVarRenaming_map, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        ambientBVarRenaming_underSubstBody,
        ambientBVarRenaming_underSubstReplacement,
        ambientBVarRenaming_map, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      have beforeEquality :
          before.map ((ambientBVarRenaming rename).map depth) =
            before.map
              (ContextSubstitution.renameAmbientBVarsAt rename depth) :=
        List.map_congr_left fun pattern _ =>
          ambientBVarRenaming_map rename depth pattern
      have afterEquality :
          after.map ((ambientBVarRenaming rename).map depth) =
            after.map
              (ContextSubstitution.renameAmbientBVarsAt rename depth) :=
        List.map_congr_left fun pattern _ =>
          ambientBVarRenaming_map rename depth pattern
      simp only [mapContext, ContextSubstitution.renameAmbientContextAt,
        inductionHypothesis, beforeEquality, afterEquality]

/-- Ordinary free-variable renaming as a structural action. -/
def freeVariableRenaming (rename : String → String) :
    StructuralPatternAction Unit where
  mapBVar _ index := index
  mapFVar _ name := rename name
  mapConstructor _ constructor := constructor
  underLambda := id
  underMultiLambda state _ := state
  underSubstBody := id
  underSubstReplacement := id

@[simp] theorem freeVariableRenaming_mapBVar (rename : String → String)
    (index : Nat) :
    (freeVariableRenaming rename).mapBVar () index = index := rfl

@[simp] theorem freeVariableRenaming_mapFVar (rename : String → String)
    (name : String) :
    (freeVariableRenaming rename).mapFVar () name = rename name := rfl

@[simp] theorem freeVariableRenaming_mapConstructor (rename : String → String)
    (constructor : String) :
    (freeVariableRenaming rename).mapConstructor () constructor =
      constructor := rfl

@[simp] theorem freeVariableRenaming_underLambda (rename : String → String) :
    (freeVariableRenaming rename).underLambda () = () := rfl

@[simp] theorem freeVariableRenaming_underMultiLambda
    (rename : String → String) (arity : Nat) :
    (freeVariableRenaming rename).underMultiLambda () arity = () := rfl

@[simp] theorem freeVariableRenaming_underSubstBody
    (rename : String → String) :
    (freeVariableRenaming rename).underSubstBody () = () := rfl

@[simp] theorem freeVariableRenaming_underSubstReplacement
    (rename : String → String) :
    (freeVariableRenaming rename).underSubstReplacement () = () := rfl

@[simp]
theorem freeVariableRenaming_map (rename : String → String)
    (pattern : Pattern) :
    (freeVariableRenaming rename).map () pattern =
      Pattern.renameFVars rename pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp only [map, Pattern.renameFVars, freeVariableRenaming_mapBVar]
  | hfvar name =>
      simp only [map, Pattern.renameFVars, freeVariableRenaming_mapFVar]
  | happly constructor arguments inductionHypothesis =>
      simp only [map, Pattern.renameFVars,
        freeVariableRenaming_mapConstructor, Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simpa only [map, Pattern.renameFVars, freeVariableRenaming_underLambda,
        Pattern.lambda.injEq, true_and] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [map, Pattern.renameFVars,
        freeVariableRenaming_underMultiLambda, Pattern.multiLambda.injEq,
        true_and] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [map, Pattern.renameFVars,
        freeVariableRenaming_underSubstBody,
        freeVariableRenaming_underSubstReplacement, Pattern.subst.injEq] using
        And.intro bodyInduction replacementInduction
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [map, Pattern.renameFVars, Pattern.collection.injEq, true_and,
        and_true]
      exact List.map_congr_left inductionHypothesis

/-- Structural free-variable renaming of the fixed syntax around a hole. -/
def renameFVarsContext (rename : String → String)
    (context : OneHoleContext) : OneHoleContext :=
  match context with
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor (before.map (Pattern.renameFVars rename))
        (renameFVarsContext rename inner)
        (after.map (Pattern.renameFVars rename))
  | .lambda binder inner =>
      .lambda binder (renameFVarsContext rename inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity binders (renameFVarsContext rename inner)
  | .substBody inner replacement =>
      .substBody (renameFVarsContext rename inner)
        (Pattern.renameFVars rename replacement)
  | .substReplacement body inner =>
      .substReplacement (Pattern.renameFVars rename body)
        (renameFVarsContext rename inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType (before.map (Pattern.renameFVars rename))
        (renameFVarsContext rename inner)
        (after.map (Pattern.renameFVars rename)) rest

@[simp]
theorem freeVariableRenaming_mapContext (rename : String → String)
    (context : OneHoleContext) :
    (freeVariableRenaming rename).mapContext () context =
      (renameFVarsContext rename context, ()) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      have beforeEquality :
          before.map ((freeVariableRenaming rename).map ()) =
            before.map (Pattern.renameFVars rename) :=
        List.map_congr_left fun pattern _ =>
          freeVariableRenaming_map rename pattern
      have afterEquality :
          after.map ((freeVariableRenaming rename).map ()) =
            after.map (Pattern.renameFVars rename) :=
        List.map_congr_left fun pattern _ =>
          freeVariableRenaming_map rename pattern
      simp only [mapContext, renameFVarsContext,
        freeVariableRenaming_mapConstructor, inductionHypothesis,
        beforeEquality, afterEquality]
  | lambda binder inner inductionHypothesis =>
      simp only [mapContext, renameFVarsContext,
        freeVariableRenaming_underLambda, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [mapContext, renameFVarsContext,
        freeVariableRenaming_underMultiLambda, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [mapContext, renameFVarsContext,
        freeVariableRenaming_underSubstBody,
        freeVariableRenaming_underSubstReplacement,
        freeVariableRenaming_map, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [mapContext, renameFVarsContext,
        freeVariableRenaming_underSubstBody,
        freeVariableRenaming_underSubstReplacement,
        freeVariableRenaming_map, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      have beforeEquality :
          before.map ((freeVariableRenaming rename).map ()) =
            before.map (Pattern.renameFVars rename) :=
        List.map_congr_left fun pattern _ =>
          freeVariableRenaming_map rename pattern
      have afterEquality :
          after.map ((freeVariableRenaming rename).map ()) =
            after.map (Pattern.renameFVars rename) :=
        List.map_congr_left fun pattern _ =>
          freeVariableRenaming_map rename pattern
      simp only [mapContext, renameFVarsContext, inductionHypothesis,
        beforeEquality, afterEquality]

end StructuralPatternAction

namespace Selects

/-- Reflect a selected occurrence through a presentation-symbol map. -/
theorem exists_preimage_mapPattern (symbols : PresentationSymbols)
    {sourceRoot targetPayload : Pattern} {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (mapPattern symbols sourceRoot)) :
    ∃ sourcePayload sourceContext,
      Selects sourcePayload sourceContext sourceRoot ∧
      CIGSLT.mapOneHoleContext symbols sourceContext = targetContext ∧
      mapPattern symbols sourcePayload = targetPayload := by
  have selected' : Selects targetPayload targetContext
      ((StructuralPatternAction.presentation symbols).map () sourceRoot) := by
    simpa only [StructuralPatternAction.presentation_map] using selected
  obtain ⟨sourcePayload, sourceContext, holeState, sourceSelected,
      contextEquality, payloadEquality⟩ :=
    (StructuralPatternAction.presentation symbols).exists_preimage_selection
      () selected'
  cases holeState
  have contextPairEquality :
      (CIGSLT.mapOneHoleContext symbols sourceContext, ()) =
        (targetContext, ()) :=
    (StructuralPatternAction.presentation_mapContext symbols sourceContext
      ).symm.trans contextEquality
  exact ⟨sourcePayload, sourceContext, sourceSelected,
    congrArg Prod.fst contextPairEquality,
    by simpa only [StructuralPatternAction.presentation_map] using
      payloadEquality⟩

/-- Reflect a selected occurrence through ambient binder renaming and retain
the exact binder depth computed at its source hole. -/
theorem exists_preimage_renameAmbientBVarsAt (rename : Nat → Nat)
    (depth : Nat) {sourceRoot targetPayload : Pattern}
    {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (ContextSubstitution.renameAmbientBVarsAt rename depth sourceRoot)) :
    ∃ sourcePayload sourceContext holeDepth,
      Selects sourcePayload sourceContext sourceRoot ∧
      ContextSubstitution.renameAmbientContextAt rename depth sourceContext =
        (targetContext, holeDepth) ∧
      ContextSubstitution.renameAmbientBVarsAt rename holeDepth sourcePayload =
        targetPayload := by
  have selected' : Selects targetPayload targetContext
      ((StructuralPatternAction.ambientBVarRenaming rename).map depth
        sourceRoot) := by
    simpa only [StructuralPatternAction.ambientBVarRenaming_map] using selected
  obtain ⟨sourcePayload, sourceContext, holeDepth, sourceSelected,
      contextEquality, payloadEquality⟩ :=
    (StructuralPatternAction.ambientBVarRenaming rename
      ).exists_preimage_selection depth selected'
  exact ⟨sourcePayload, sourceContext, holeDepth, sourceSelected,
    (StructuralPatternAction.ambientBVarRenaming_mapContext rename depth
      sourceContext).symm.trans contextEquality,
    by simpa only [StructuralPatternAction.ambientBVarRenaming_map] using
      payloadEquality⟩

/-- Reflect a selected occurrence through a possibly non-injective
free-variable renaming. -/
theorem exists_preimage_renameFVars (rename : String → String)
    {sourceRoot targetPayload : Pattern} {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (Pattern.renameFVars rename sourceRoot)) :
    ∃ sourcePayload sourceContext,
      Selects sourcePayload sourceContext sourceRoot ∧
      StructuralPatternAction.renameFVarsContext rename sourceContext =
        targetContext ∧
      Pattern.renameFVars rename sourcePayload = targetPayload := by
  have selected' : Selects targetPayload targetContext
      ((StructuralPatternAction.freeVariableRenaming rename).map ()
        sourceRoot) := by
    simpa only [StructuralPatternAction.freeVariableRenaming_map] using selected
  obtain ⟨sourcePayload, sourceContext, holeState, sourceSelected,
      contextEquality, payloadEquality⟩ :=
    (StructuralPatternAction.freeVariableRenaming rename
      ).exists_preimage_selection () selected'
  cases holeState
  have contextPairEquality :
      (StructuralPatternAction.renameFVarsContext rename sourceContext, ()) =
        (targetContext, ()) :=
    (StructuralPatternAction.freeVariableRenaming_mapContext rename
      sourceContext).symm.trans contextEquality
  exact ⟨sourcePayload, sourceContext, sourceSelected,
    congrArg Prod.fst contextPairEquality,
    by simpa only [StructuralPatternAction.freeVariableRenaming_map] using
      payloadEquality⟩

/-- Positive canary: a mapped occurrence retains the exact mapped zipper. -/
def mapPattern (symbols : PresentationSymbols)
    {sourcePayload sourceRoot : Pattern} {sourceContext : OneHoleContext}
    (selected : Selects sourcePayload sourceContext sourceRoot) :
    Selects (Mettapedia.GSLT.LanguageDef.mapPattern symbols sourcePayload)
      (CIGSLT.mapOneHoleContext symbols sourceContext)
      (Mettapedia.GSLT.LanguageDef.mapPattern symbols sourceRoot) := by
  simpa only [StructuralPatternAction.presentation_map,
    StructuralPatternAction.presentation_mapContext] using
    (StructuralPatternAction.presentation symbols).mapSelection () selected

end Selects

/-- Non-injectivity canary: structural occurrence reflection cannot promise a
unique source spelling when the free-variable map coalesces names. -/
theorem renameFVars_constant_not_injective :
    ¬ Function.Injective
      (Pattern.renameFVars (fun _ => "semantic-atom")) := by
  intro injective
  have equality : (Pattern.fvar "left") = .fvar "right" :=
    injective (by simp [Pattern.renameFVars])
  simp at equality

end Mettapedia.GSLT.LanguageDef
