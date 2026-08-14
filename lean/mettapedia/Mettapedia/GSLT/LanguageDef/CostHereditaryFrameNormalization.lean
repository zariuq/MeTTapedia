import Mettapedia.GSLT.LanguageDef.CostSemanticAtom
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Hereditary semantic-atom normalization of Cost frames

A selected static frame is first rewritten over finite semantic atoms.  The
atoms stand for already-normalized child regions and retagged source
parameters; their original serialized names are not canonicalization keys.
After the selected frame canonicalizes, a quote-aware supported restoration
reinstalls the typed atom values.

This module establishes the local exactness boundary of that construction.
It deliberately does not claim that reification is injective: distinct
occurrence origins may denote one semantic atom.  Instead, restoring a
reified frame agrees exactly with evaluating the original finite parameter
environment.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace CostStaticBinderThinning

/-- Ambient binder insertion changes de Bruijn indices but preserves every
ordinary free-variable name. -/
@[simp]
theorem freeFvarNames_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (pattern : Pattern) :
    (thinning.thickenAmbientBVars depth pattern).freeFvarNames =
      pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | hfvar name =>
      simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      simp only [thickenAmbientBVars, Pattern.freeFvarNames,
        List.flatMap_map]
      exact List.flatMap_congr fun argument membership =>
        inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simpa [thickenAmbientBVars, Pattern.freeFvarNames] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [thickenAmbientBVars, Pattern.freeFvarNames] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [thickenAmbientBVars, Pattern.freeFvarNames,
        bodyInduction (depth + 1), replacementInduction depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [thickenAmbientBVars, Pattern.freeFvarNames,
        List.flatMap_map]
      rw [List.flatMap_congr fun element membership =>
        inductionHypothesis element membership depth]

/-- Ambient binder insertion changes only bound-variable indices and hence
preserves every constructor fragment.  This is the constructor-side companion
to `freeFvarNames_thickenAmbientBVars`; together they isolate the two pieces of
syntax used by semantic-atom reification. -/
theorem constructorsWithin_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    {allowed : String -> Prop} {pattern : Pattern}
    (supported : ConstructorsWithin allowed pattern) (depth : Nat) :
    ConstructorsWithin allowed (thinning.thickenAmbientBVars depth pattern) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [thickenAmbientBVars]
  | hfvar name => simp [thickenAmbientBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [thickenAmbientBVars, constructorsWithin_apply]
      exact ⟨supported.1, supported.2.map fun argument membership =>
        inductionHypothesis argument membership
          (supported.2.of_mem membership) depth⟩
  | hlambda binder body inductionHypothesis =>
      simpa only [thickenAmbientBVars, constructorsWithin_lambda] using
        inductionHypothesis supported (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [thickenAmbientBVars, constructorsWithin_multiLambda] using
        inductionHypothesis supported (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [thickenAmbientBVars, constructorsWithin_subst] using
        And.intro (bodyInduction supported.1 (depth + 1))
          (replacementInduction supported.2 depth)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [thickenAmbientBVars, constructorsWithin_collection]
      exact supported.map fun element membership =>
        inductionHypothesis element membership
          (supported.of_mem membership) depth

end CostStaticBinderThinning

namespace CostStaticAtomEnvironment

/-- Replace one original rigid-parameter name by its canonical finite atom
name.  A name outside the frame inventory is preserved; admitted target
frames prove that this fallback is unreachable at every `Pattern.fvar`.
-/
def reifyName {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (name : String) : String :=
  match environment.slotOfName? name with
  | some slot => environment.atomName slot
  | none => name

/-- Structural assignment underlying atom reification.  Its values are rigid
free variables, so de Bruijn weakening and quote-depth resets leave them
unchanged. -/
def reificationAssignment {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ContextSupport.Assignment :=
  fun name => .fvar (environment.reifyName name)

/-- Structurally reify every ordinary free-variable occurrence through the
finite semantic quotient.  Bound indices, constructors, binder metadata, and
collection tails are untouched. -/
def reify {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar (environment.reifyName name)
  | .apply constructor arguments =>
      .apply constructor (arguments.map environment.reify)
  | .lambda binder body => .lambda binder (environment.reify body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (environment.reify body)
  | .subst body replacement =>
      .subst (environment.reify body) (environment.reify replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (elements.map environment.reify) rest
termination_by pattern => sizeOf pattern

/-- Reify every fixed pattern of a one-hole context through the finite
semantic-atom environment while retaining the unique hole.  This is the
context-level first stage of frame transport: original source names become
endpoint atom names before a semantic-key cospan moves them to a common
namespace. -/
def reifyContext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor (before.map environment.reify)
        (environment.reifyContext inner) (after.map environment.reify)
  | .lambda binder inner =>
      .lambda binder (environment.reifyContext inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity binders (environment.reifyContext inner)
  | .substBody inner replacement =>
      .substBody (environment.reifyContext inner)
        (environment.reify replacement)
  | .substReplacement body inner =>
      .substReplacement (environment.reify body)
        (environment.reifyContext inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType (before.map environment.reify)
        (environment.reifyContext inner) (after.map environment.reify) rest

/-- Environment reification commutes with filling a one-hole context.  The
hole occurrence is therefore transported exactly once, independently of all
fixed siblings retained by the context. -/
theorem reifyContext_fill
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (context : OneHoleContext) (pattern : Pattern) :
    (environment.reifyContext context).fill (environment.reify pattern) =
      environment.reify (context.fill pattern) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, List.map_append,
        inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [reifyContext, OneHoleContext.fill, reify, List.map_append,
        inductionHypothesis]

/-- Transport one exact free-variable occurrence through semantic-atom
reification.  The zipper remains proof-relevant even when distinct source
names later denote the same semantic atom; only the selected leaf name is
reified. -/
noncomputable def reifyOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    CostStaticFVarOccurrence (environment.reify root) :=
  { name := environment.reifyName occurrence.name
    context := environment.reifyContext occurrence.context
    selected := by
      have filled :
          (environment.reifyContext occurrence.context).fill
              (.fvar (environment.reifyName occurrence.name)) =
            environment.reify root := by
        calc
          (environment.reifyContext occurrence.context).fill
                (.fvar (environment.reifyName occurrence.name)) =
              (environment.reifyContext occurrence.context).fill
                (environment.reify (.fvar occurrence.name)) := by
            simp [reify]
          _ = environment.reify
                (occurrence.context.fill (.fvar occurrence.name)) :=
            environment.reifyContext_fill occurrence.context
              (.fvar occurrence.name)
          _ = environment.reify root :=
            congrArg environment.reify occurrence.selected.fill_eq
      rw [← filled]
      exact Selects.of_fill (environment.reifyContext occurrence.context)
        (.fvar (environment.reifyName occurrence.name)) }

@[simp]
theorem reifyOccurrence_name
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    (environment.reifyOccurrence occurrence).name =
      environment.reifyName occurrence.name := rfl

@[simp]
theorem reifyOccurrence_context
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    (environment.reifyOccurrence occurrence).context =
      environment.reifyContext occurrence.context := rfl

/-- If the original occurrence is represented by a concrete finite atom
slot, its transported occurrence names exactly that slot.  This statement
keeps the zipper and the quotient lookup separate. -/
theorem reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.reifyOccurrence occurrence).name =
      environment.atomName slot := by
  simp [reifyName, selected]

/-- Semantic-atom reification is natural with respect to every structural
presentation-symbol map: the map changes constructors and sorts, while
reification changes only ordinary free-variable names. -/
@[simp]
theorem reify_mapPattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (symbols : PresentationSymbols) (pattern : Pattern) :
    environment.reify (mapPattern symbols pattern) =
      mapPattern symbols (environment.reify pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, reify]
  | hfvar name => simp [mapPattern, reify]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, reify, List.map_map,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, reify, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, reify, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [mapPattern, reify, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, reify, List.map_map,
        Pattern.collection.injEq, true_and]
      exact ⟨List.map_congr_left (fun element membership =>
        inductionHypothesis element membership), trivial⟩

/-- Semantic-atom reification commutes with ambient-binder insertion because
the two traversals act on disjoint syntax: free names versus de Bruijn
indices. -/
@[simp]
theorem reify_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (pattern : Pattern) :
    environment.reify (thinning.thickenAmbientBVars depth pattern) =
      thinning.thickenAmbientBVars depth (environment.reify pattern) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reify]
  | hfvar name =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reify]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticBinderThinning.thickenAmbientBVars, reify,
        List.map_map, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reify,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reify,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [CostStaticBinderThinning.thickenAmbientBVars, reify,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticBinderThinning.thickenAmbientBVars, reify,
        List.map_map, Pattern.collection.injEq, true_and]
      exact ⟨List.map_congr_left (fun element membership =>
        inductionHypothesis element membership depth), trivial⟩

/-- Semantic-atom reification changes no locally nameless binder metadata. -/
@[simp]
theorem hasCanonicalBinderMetadata_reify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (pattern : Pattern) :
    (environment.reify pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reify, Pattern.hasCanonicalBinderMetadata]
  | hfvar name => simp [reify, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [reify, Pattern.hasCanonicalBinderMetadata]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons,
            Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg (argument.hasCanonicalBinderMetadata && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])
  | hlambda binder body inductionHypothesis =>
      simp [reify, Pattern.hasCanonicalBinderMetadata, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [reify, Pattern.hasCanonicalBinderMetadata, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [reify, Pattern.hasCanonicalBinderMetadata, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, Pattern.hasCanonicalBinderMetadata]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons,
            Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis element (by simp)]
          apply congrArg (element.hasCanonicalBinderMetadata && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])

/-- Reification neither introduces explicit substitution syntax nor opens a
collection tail. -/
@[simp]
theorem isObjectPattern_reify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (pattern : Pattern) :
    WellSorted.isObjectPattern (environment.reify pattern) =
      WellSorted.isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reify, WellSorted.isObjectPattern]
  | hfvar name => simp [reify, WellSorted.isObjectPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [reify, WellSorted.isObjectPattern]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons, WellSorted.isObjectPatternList]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg (WellSorted.isObjectPattern argument && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])
  | hlambda binder body inductionHypothesis =>
      simpa [reify, WellSorted.isObjectPattern] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [reify, WellSorted.isObjectPattern] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [reify, WellSorted.isObjectPattern]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, WellSorted.isObjectPattern]
      have listEquality :
          WellSorted.isObjectPatternList
              (elements.map environment.reify) =
            WellSorted.isObjectPatternList elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, WellSorted.isObjectPatternList]
            rw [inductionHypothesis element (by simp)]
            apply congrArg (WellSorted.isObjectPattern element && ·)
            apply listInduction
            intro other membership
            exact inductionHypothesis other (by simp [membership])
      rw [listEquality]

/-- Reification preserves every reflective quotation boundary because it
changes only ordinary free-variable spellings. -/
@[simp]
theorem binderSafeAt_reify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    binderSafeAt quoteConstructor depth (environment.reify pattern) =
      binderSafeAt quoteConstructor depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [reify, binderSafeAt]
  | hfvar name => simp [reify, binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      have listEquality : ∀ localDepth,
          binderSafeListAt quoteConstructor localDepth
              (arguments.map environment.reify) =
            binderSafeListAt quoteConstructor localDepth arguments := by
        intro localDepth
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, binderSafeListAt]
            rw [inductionHypothesis argument (by simp)]
            apply congrArg
              (binderSafeAt quoteConstructor localDepth argument && ·)
            apply listInduction
            intro other membership otherDepth
            exact inductionHypothesis other (by simp [membership]) otherDepth
      cases arguments with
      | nil => simp [reify, binderSafeAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              simp only [reify, List.map_cons, List.map_nil, binderSafeAt]
              split
              · exact inductionHypothesis argument (by simp) 0
              · exact listEquality depth
          | cons second arguments =>
              simpa [reify, binderSafeAt] using listEquality depth
  | hlambda binder body inductionHypothesis =>
      simpa [reify, binderSafeAt] using inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [reify, binderSafeAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [reify, binderSafeAt, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, binderSafeAt]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, binderSafeListAt]
          rw [inductionHypothesis element (by simp)]
          apply congrArg
            (binderSafeAt quoteConstructor depth element && ·)
          apply listInduction
          intro other membership otherDepth
          exact inductionHypothesis other (by simp [membership]) otherDepth

/-- The direct structural reifier is exactly reflective supported
substitution by rigid atom variables, at every available quote depth. -/
theorem reify_eq_substituteAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    (availableDepth : Nat) (pattern : Pattern) :
    environment.reify pattern =
      ReflectiveContextSupport.substituteAt profile
        (fun _ => []) environment.reificationAssignment availableDepth
        pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [reify, ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      simp [reify, reificationAssignment,
        ReflectiveContextSupport.substituteAt, liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [reify, ReflectiveContextSupport.substituteAt]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership _
  | hlambda binder body inductionHypothesis =>
      simp only [reify, ReflectiveContextSupport.substituteAt]
      congr 1
      exact inductionHypothesis _
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [reify, ReflectiveContextSupport.substituteAt]
      congr 1
      exact inductionHypothesis _
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [reify, ReflectiveContextSupport.substituteAt]
      congr 1
      · exact bodyInduction _
      · exact replacementInduction _
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, ReflectiveContextSupport.substituteAt]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership _

/-- Restore a reified frame at the binder depth visible since the nearest
authored quote boundary. -/
def restoreAt {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (availableDepth : Nat) (pattern : Pattern) : Pattern :=
  ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
    environment.restorationSupport environment.restorationAssignment
    availableDepth pattern

/-- Top-level restoration in an explicit target binder context. -/
def restore {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (bound : List TypeExpr) (pattern : Pattern) : Pattern :=
  environment.restoreAt bound.length pattern

/-- A binder-closed semantic atom restores to its stored normalized value at
every ambient depth.  The support component may be nonempty: closedness makes
the weakening selected by that support observationally inert. -/
theorem restoreAt_atomName_eq_normal_of_scoped
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount)
    (normalScoped :
      (environment.atomValue slot).key.normal.isWellScopedAt 0 = true)
    (depth : Nat) :
    environment.restoreAt depth (.fvar (environment.atomName slot)) =
      (environment.atomValue slot).key.normal := by
  simp only [CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt,
    environment.restorationSupport_atomName,
    environment.restorationAssignment_atomName]
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
    normalScoped

/-- A semantic atom whose retained target-support length is exactly the
ambient restoration depth restores to its normalized value without any
closedness premise.  This is the ordinary, non-quote boundary case: the
weakening offset is definitionally zero, so bound indices are preserved. -/
theorem restoreAt_atomName_eq_normal_of_support_length_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) (depth : Nat)
    (supportLength :
      (environment.atomValue slot).key.targetSupport.length = depth) :
    environment.restoreAt depth (.fvar (environment.atomName slot)) =
      (environment.atomValue slot).key.normal := by
  simp only [CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt,
    environment.restorationSupport_atomName,
    environment.restorationAssignment_atomName]
  rw [supportLength]
  rw [Nat.sub_self]
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero
    (environment.atomValue slot).key.normal 0

/-- Bound-context wrapper around
`CostStaticAtomEnvironment.restoreAt_atomName_eq_normal_of_scoped`. -/
theorem restore_atomName_eq_normal_of_scoped
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount)
    (normalScoped :
      (environment.atomValue slot).key.normal.isWellScopedAt 0 = true)
    (bound : List TypeExpr) :
    environment.restore bound (.fvar (environment.atomName slot)) =
      (environment.atomValue slot).key.normal :=
  environment.restoreAt_atomName_eq_normal_of_scoped slot normalScoped
    bound.length

/-- Bound-context wrapper around
`CostStaticAtomEnvironment.restoreAt_atomName_eq_normal_of_support_length_eq`. -/
theorem restore_atomName_eq_normal_of_support_length_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) (bound : List TypeExpr)
    (supportLength :
      (environment.atomValue slot).key.targetSupport.length = bound.length) :
    environment.restore bound (.fvar (environment.atomName slot)) =
      (environment.atomValue slot).key.normal :=
  environment.restoreAt_atomName_eq_normal_of_support_length_eq slot
    bound.length supportLength

/-- Free typing context of a reified frame.  Only canonical atom names are
accepted; original boundary/source spellings have no authority after
reification. -/
def atomFreeContext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    WellSorted.FreeTypeContext :=
  fun name => (environment.lookupAtom? name).map fun slot =>
    (environment.atomValue slot).key.targetType

/-- Authored source typing context of an atomized frame.  It is distinct
from `atomFreeContext`: the former carries source types into the sole authored
canonical section, while the latter types the generated frame obtained after
the selected Cost symbol map. -/
def sourceAtomFreeContext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    WellSorted.FreeTypeContext :=
  fun name => (environment.lookupAtom? name).map fun slot =>
    (environment.atomValue slot).key.sourceType

/-- Reflective support presented to the authored canonical section after
atomization.  It remains in the generated binder codomain, exactly as the
certified source-region support does. -/
def sourceAtomSupport {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ContextSupport.Support := fun name =>
  match environment.lookupAtom? name with
  | some slot => (environment.atomValue slot).key.targetSupport
  | none => []

@[simp]
theorem atomFreeContext_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.atomFreeContext (environment.atomName slot) =
      some (environment.atomValue slot).key.targetType := by
  simp [atomFreeContext]

@[simp]
theorem sourceAtomFreeContext_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.sourceAtomFreeContext (environment.atomName slot) =
      some (environment.atomValue slot).key.sourceType := by
  simp [sourceAtomFreeContext]

@[simp]
theorem sourceAtomSupport_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount) :
    environment.sourceAtomSupport (environment.atomName slot) =
      (environment.atomValue slot).key.targetSupport := by
  simp [sourceAtomSupport]

/-- A fiber-coherent semantic environment maps its authored atom context
exactly to the generated target atom context. -/
theorem sourceAtomFreeContext_map_eq_atomFreeContext
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols source)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType) :
    environment.sourceAtomFreeContext.map (color.symbols source) =
      environment.atomFreeContext := by
  funext name
  simp only [WellSorted.FreeTypeContext.map, sourceAtomFreeContext,
    atomFreeContext]
  cases selected : environment.lookupAtom? name with
  | none => simp
  | some slot => simp [typeMap slot]

/-- The source and restoration support functions are definitionally the same
generated binder suffix, viewed on opposite sides of the Cost symbol map. -/
theorem sourceAtomSupport_eq_restorationSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    environment.sourceAtomSupport = environment.restorationSupport := by
  rfl

/-- Restoring semantic atoms is a genuine typed open assignment.  Failure to
decode an atom name is impossible whenever the finite source context contains
that name. -/
def restorationSupportedOpenAssignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    WellSorted.SupportedOpenAssignment source.costWholeReflectionProfile
      source.costWholeLanguage
      environment.atomFreeContext targetFree environment.restorationSupport
    where
  assignment := environment.restorationAssignment
  typed := by
    intro name type lookup
    simp only [atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        simp only [selected, Option.map_some] at lookup
        have typeEquality : (environment.atomValue slot).key.targetType = type :=
          Option.some.inj lookup
        cases typeEquality
        simpa [restorationSupport, restorationAssignment, selected] using
          (environment.atomValue slot).normalTyped
  canonicalBinderMetadata := by
    intro name type lookup
    simp only [atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        simpa [restorationAssignment, selected] using
          (environment.atomValue slot).normalCanonicalBinderMetadata
  objectPattern := by
    intro name type lookup
    simp only [atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        simpa [restorationAssignment, selected] using
          (environment.atomValue slot).normalObject
  reflectiveScopeSafe := by
    intro name type lookup
    simp only [atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        simpa [restorationSupport, restorationAssignment, selected] using
          (environment.atomValue slot).normalReflectiveScopeSafe

/-- Reifying a support-safe typed pattern preserves both its typing and its
reflective-support certificate, provided every free-variable occurrence is
represented in the finite positional inventory.  The coverage hypothesis is
intentionally occurrence-local: unused ambient context entries acquire no
atom and no authority. -/
private theorem reifySupportSafeAux
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {sourceFree atomFree : WellSorted.FreeTypeContext}
    {sourceSupport atomSupport : ContextSupport.Support}
    (mapsLookup : ∀ (occurrence : CostStaticFVarOccurrence root)
      (slot : Fin environment.atomCount),
      environment.slotOfName? occurrence.name = some slot →
      ∀ {type}, sourceFree occurrence.name = some type →
        atomFree (environment.atomName slot) = some type)
    (mapsSupport : ∀ (occurrence : CostStaticFVarOccurrence root)
      (slot : Fin environment.atomCount),
      environment.slotOfName? occurrence.name = some slot →
      atomSupport (environment.atomName slot) =
        sourceSupport occurrence.name)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType language
      sourceFree bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile sourceSupport
      available binderImage)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    ∃ retyped : WellSorted.HasType language
        atomFree bound (environment.reify pattern) type,
      retyped.ReflectiveSupportSafeAt profile atomSupport
        available binderImage := by
  exact WellSorted.HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type} typed available currentImage _ =>
      (∀ name, name ∈ pattern.freeFvarNames →
        ∃ occurrence : CostStaticFVarOccurrence root,
          occurrence.name = name) →
      ∃ retyped : WellSorted.HasType language
          atomFree bound (environment.reify pattern) type,
        retyped.ReflectiveSupportSafeAt profile atomSupport
          available currentImage)
    (motive_2 := fun {bound arguments parameters} typed available
        currentImage _ =>
      (∀ name, name ∈ arguments.flatMap Pattern.freeFvarNames →
        ∃ occurrence : CostStaticFVarOccurrence root,
          occurrence.name = name) →
      ∃ retyped : WellSorted.ArgumentsHaveTypes language
          atomFree bound
          (arguments.map environment.reify) parameters,
        retyped.ReflectiveSupportSafeAt profile atomSupport
          available currentImage)
    (motive_3 := fun {bound elements elementType} typed available
        currentImage _ =>
      (∀ name, name ∈ elements.flatMap Pattern.freeFvarNames →
        ∃ occurrence : CostStaticFVarOccurrence root,
          occurrence.name = name) →
      ∃ retyped : WellSorted.ElementsHaveType language
          atomFree bound
          (elements.map environment.reify) elementType,
        retyped.ReflectiveSupportSafeAt profile atomSupport
          available currentImage)
    (by
      intro bound index type lookup available currentImage _covered
      let retyped := WellSorted.HasType.bvar
        (language := language)
        (free := atomFree) lookup
      simpa [reify] using
        (⟨retyped, WellSorted.HasType.ReflectiveSupportSafeAt.bvar
          lookup available⟩))
    (by
      intro bound name type lookup available currentImage shape covered
      obtain ⟨occurrence, occurrenceName⟩ :=
        covered name (by simp [Pattern.freeFvarNames])
      obtain ⟨slot, selectedOccurrence⟩ := Option.isSome_iff_exists.mp
        (environment.slotOfName?_isSome_of_occurrence occurrence)
      have selected : environment.slotOfName? name = some slot := by
        simpa [occurrenceName] using selectedOccurrence
      have sourceLookup : sourceFree occurrence.name = some type := by
        simpa [occurrenceName] using lookup
      have atomLookup : atomFree (environment.atomName slot) = some type :=
        mapsLookup occurrence slot selectedOccurrence sourceLookup
      have supportEquality : atomSupport (environment.atomName slot) =
          sourceSupport name := by
        simpa [occurrenceName] using
          mapsSupport occurrence slot selectedOccurrence
      obtain ⟨inner, availableShape⟩ := shape
      let retyped := WellSorted.HasType.fvar
        (language := language) (bound := bound) atomLookup
      have retypedSafe : retyped.ReflectiveSupportSafeAt
          profile atomSupport available currentImage := by
        refine .fvar atomLookup available ⟨inner, ?_⟩
        simpa [supportEquality] using availableShape
      simpa [reify, reifyName, selected] using ⟨retyped, retypedSafe⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage quoted argumentsSafe argumentsIH covered
      obtain ⟨retyped, retypedSafe⟩ := argumentsIH (by
        intro name nameMembership
        apply covered name
        simpa [Pattern.freeFvarNames] using nameMembership)
      let result := WellSorted.HasType.constructor membership notBare retyped
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
          (membership := membership) (notBare := notBare) quoted
          retypedSafe⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage ordinary argumentsSafe argumentsIH covered
      obtain ⟨retyped, retypedSafe⟩ := argumentsIH (by
        intro name nameMembership
        apply covered name
        simpa [Pattern.freeFvarNames] using nameMembership)
      let result := WellSorted.HasType.constructor membership notBare retyped
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
          (membership := membership) (notBare := notBare) ordinary
          retypedSafe⟩)
    (by
      intro bound binder body domain codomain bodyTyped available currentImage
        bodySafe bodyIH covered
      obtain ⟨retyped, retypedSafe⟩ := bodyIH (by
        intro name nameMembership
        apply covered name
        simpa [Pattern.freeFvarNames] using nameMembership)
      let result := WellSorted.HasType.lambda (binder := binder) retyped
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.lambda
          retypedSafe⟩)
    (by
      intro bound arity binders body domain codomain bodyTyped available
        currentImage bodySafe bodyIH covered
      obtain ⟨retyped, retypedSafe⟩ := bodyIH (by
        intro name nameMembership
        apply covered name
        simpa [Pattern.freeFvarNames] using nameMembership)
      let result := WellSorted.HasType.multiLambda
        (binders := binders) retyped
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.multiLambda
          retypedSafe⟩)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        available currentImage bodySafe replacementSafe bodyIH replacementIH
        covered
      obtain ⟨retypedBody, retypedBodySafe⟩ := bodyIH (by
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership])
      obtain ⟨retypedReplacement, retypedReplacementSafe⟩ :=
        replacementIH (by
          intro name nameMembership
          apply covered name
          simp [Pattern.freeFvarNames, nameMembership])
      let result := WellSorted.HasType.subst retypedBody retypedReplacement
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.subst
          retypedBodySafe retypedReplacementSafe⟩)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        available currentImage elementsSafe elementsIH covered
      obtain ⟨retyped, retypedSafe⟩ := elementsIH (by
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership])
      let result := WellSorted.HasType.collection
        (collectionType := collectionType) (rest := rest) retyped
      simpa [reify] using
        ⟨result, WellSorted.HasType.ReflectiveSupportSafeAt.collection
          retypedSafe⟩)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available currentImage
        elementsSafe elementsIH covered
      obtain ⟨retyped, retypedSafe⟩ := elementsIH (by
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership])
      let result := WellSorted.HasType.collectionConstructor
        (rest := rest) membership parameterShape retyped
      simpa [reify] using
        ⟨result,
          WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
            (parameterName := parameterName) (membership := membership)
            (parameterShape := parameterShape) retypedSafe⟩)
    (by
      intro bound available currentImage _covered
      let retyped := WellSorted.ArgumentsHaveTypes.nil
        (language := language)
        (free := atomFree) (bound := bound)
      exact ⟨retyped, .nil bound available⟩)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        currentImage argumentSafe argumentsSafe argumentIH argumentsIH covered
      obtain ⟨retypedArgument, retypedArgumentSafe⟩ := argumentIH (by
        intro name nameMembership
        apply covered name
        simp [nameMembership])
      obtain ⟨retypedArguments, retypedArgumentsSafe⟩ := argumentsIH (by
        intro name nameMembership
        apply covered name
        simp [nameMembership])
      have reifiedRepresentation :
          WellSorted.MatchesParameterRepresentation parameter
            (environment.reify argument) := by
        rw [environment.reify_eq_substituteAt (profile := profile)
          available.length argument]
        exact WellSorted.MatchesParameterRepresentation.substituteReflectiveAt
          profile parameter argument (fun _ => [])
            environment.reificationAssignment available.length representation
      let result := WellSorted.ArgumentsHaveTypes.cons reifiedRepresentation
        parameterType retypedArgument retypedArguments
      refine ⟨result, ?_⟩
      exact .cons (representation := reifiedRepresentation)
        (parameterType := parameterType) retypedArgumentSafe
        retypedArgumentsSafe)
    (by
      intro bound elementType available currentImage _covered
      let retyped := WellSorted.ElementsHaveType.nil
        (language := language)
        (free := atomFree) bound elementType
      exact ⟨retyped, .nil bound elementType available⟩)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available currentImage elementSafe elementsSafe elementIH elementsIH
        covered
      obtain ⟨retypedElement, retypedElementSafe⟩ := elementIH (by
        intro name nameMembership
        apply covered name
        simp [nameMembership])
      obtain ⟨retypedElements, retypedElementsSafe⟩ := elementsIH (by
        intro name nameMembership
        apply covered name
        simp [nameMembership])
      let result := WellSorted.ElementsHaveType.cons retypedElement
        retypedElements
      refine ⟨result, ?_⟩
      exact
        (WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.cons
          retypedElementSafe retypedElementsSafe).castTyping)
    safe covered

/-- Public support-aware reification law for any covered subpattern of the
certified occurrence root. -/
theorem reify_reflectiveSupportSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType source.costWholeLanguage
      table.mappedFreeContext bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile
      table.restorationSupport
      available binderImage)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    ∃ retyped : WellSorted.HasType source.costWholeLanguage
        environment.atomFreeContext bound (environment.reify pattern) type,
      retyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        environment.restorationSupport
        available binderImage :=
  reifySupportSafeAux environment
    (by
      intro occurrence slot selected type lookup
      have aligned :=
        environment.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
          occurrence slot selected
      have typeEquality : (environment.atomValue slot).key.targetType = type :=
        Option.some.inj (aligned.symm.trans lookup)
      rw [environment.atomFreeContext_atomName, typeEquality])
    (by
      intro occurrence slot selected
      rw [environment.restorationSupport_atomName]
      exact
        environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
          occurrence slot selected)
    safe covered

/-- Source-fiber specialization of support-aware reification.  The result is
ready for the sole authored `openCanonical` section: atom source types inhabit
the source language, while support remains interpreted through the selected
Cost binder image. -/
theorem reify_sourceReflectiveSupportSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      table.sourceFreeContext bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.reflection.1
      table.sourceSupport
      available binderImage)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    ∃ retyped : WellSorted.HasType
        source.theory.presentation.presentation.language
        environment.sourceAtomFreeContext bound (environment.reify pattern)
        type,
      retyped.ReflectiveSupportSafeAt source.reflection.1
        environment.sourceAtomSupport
        available binderImage := by
  exact reifySupportSafeAux environment
    (by
      intro occurrence slot selected type lookup
      have aligned :=
        environment.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
          occurrence slot selected
      have typeEquality : (environment.atomValue slot).key.sourceType = type :=
        Option.some.inj (aligned.symm.trans lookup)
      rw [environment.sourceAtomFreeContext_atomName, typeEquality])
    (by
      intro occurrence slot selected
      rw [environment.sourceAtomSupport_atomName]
      exact
        environment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          occurrence slot selected)
    safe covered

mutual
  /-- Constructor-aware source typing is preserved by semantic-atom
  reification on every occurrence-covered subpattern.  Bare collections keep
  the exact authored declaration recorded by the input derivation. -/
  private theorem reifySourceHasTypeWithConstructorsAux
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
      {root : Pattern}
      {inventory : CostStaticParameterInventory source color targetFree table
        values root}
      (environment : CostStaticAtomEnvironment source color targetFree inventory)
      {allowed : String → Prop} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasTypeWithConstructors
        source.theory.presentation.presentation.language allowed
        table.sourceFreeContext bound pattern type)
      (covered : ∀ name, name ∈ pattern.freeFvarNames →
        ∃ occurrence : CostStaticFVarOccurrence root,
          occurrence.name = name) :
      WellSorted.HasTypeWithConstructors
        source.theory.presentation.presentation.language allowed
        environment.sourceAtomFreeContext bound
        (environment.reify pattern) type := by
    cases typed with
    | bvar lookup =>
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.bvar
            (allowed := allowed) (free := environment.sourceAtomFreeContext)
            lookup)
    | @fvar bound name type lookup =>
        obtain ⟨occurrence, occurrenceName⟩ :=
          covered name (by simp [Pattern.freeFvarNames])
        obtain ⟨slot, selectedOccurrence⟩ := Option.isSome_iff_exists.mp
          (environment.slotOfName?_isSome_of_occurrence occurrence)
        have selected : environment.slotOfName? occurrence.name = some slot :=
          selectedOccurrence
        have selectedAtName : environment.slotOfName? name = some slot := by
          simpa [occurrenceName] using selected
        have aligned :=
          environment.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
            occurrence slot selected
        have sourceLookup : table.sourceFreeContext occurrence.name =
            some type := by
          simpa [occurrenceName] using lookup
        have typeEquality : (environment.atomValue slot).key.sourceType = type :=
          Option.some.inj (aligned.symm.trans sourceLookup)
        have atomLookup : environment.sourceAtomFreeContext
            (environment.atomName slot) = some type := by
          rw [environment.sourceAtomFreeContext_atomName, typeEquality]
        have retyped := WellSorted.HasTypeWithConstructors.fvar
          (language := source.theory.presentation.presentation.language)
          (allowed := allowed) (bound := bound) atomLookup
        simpa [reify, reifyName, selectedAtName] using retyped
    | constructor allowedLabel membership notBare argumentsTyped =>
        have retypedArguments :=
          reifySourceArgumentsHaveTypesWithConstructorsAux environment
            argumentsTyped (by
              intro name nameMembership
              apply covered name
              simpa [Pattern.freeFvarNames] using nameMembership)
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.constructor allowedLabel
            membership notBare retypedArguments)
    | lambda bodyTyped =>
        have retypedBody :=
          reifySourceHasTypeWithConstructorsAux environment bodyTyped (by
            intro name nameMembership
            apply covered name
            simpa [Pattern.freeFvarNames] using nameMembership)
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.lambda retypedBody)
    | multiLambda bodyTyped =>
        have retypedBody :=
          reifySourceHasTypeWithConstructorsAux environment bodyTyped (by
            intro name nameMembership
            apply covered name
            simpa [Pattern.freeFvarNames] using nameMembership)
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.multiLambda retypedBody)
    | subst bodyTyped replacementTyped =>
        have retypedBody :=
          reifySourceHasTypeWithConstructorsAux environment bodyTyped (by
            intro name nameMembership
            apply covered name
            simp [Pattern.freeFvarNames, nameMembership])
        have retypedReplacement :=
          reifySourceHasTypeWithConstructorsAux environment replacementTyped (by
            intro name nameMembership
            apply covered name
            simp [Pattern.freeFvarNames, nameMembership])
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.subst retypedBody
            retypedReplacement)
    | collection elementsTyped =>
        have retypedElements :=
          reifySourceElementsHaveTypeWithConstructorsAux environment
            elementsTyped (by
              intro name nameMembership
              apply covered name
              simp [Pattern.freeFvarNames, nameMembership])
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.collection retypedElements)
    | collectionConstructor allowedLabel membership parameterShape
        elementsTyped =>
        have retypedElements :=
          reifySourceElementsHaveTypeWithConstructorsAux environment
            elementsTyped (by
              intro name nameMembership
              apply covered name
              simp [Pattern.freeFvarNames, nameMembership])
        simpa [reify] using
          (WellSorted.HasTypeWithConstructors.collectionConstructor
            allowedLabel membership parameterShape retypedElements)

  /-- Ordered-argument companion to constructor-aware atom reification. -/
  private theorem reifySourceArgumentsHaveTypesWithConstructorsAux
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
      {root : Pattern}
      {inventory : CostStaticParameterInventory source color targetFree table
        values root}
      (environment : CostStaticAtomEnvironment source color targetFree inventory)
      {allowed : String → Prop} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypesWithConstructors
        source.theory.presentation.presentation.language allowed
        table.sourceFreeContext bound arguments parameters)
      (covered : ∀ name,
        name ∈ arguments.flatMap Pattern.freeFvarNames →
          ∃ occurrence : CostStaticFVarOccurrence root,
            occurrence.name = name) :
      WellSorted.ArgumentsHaveTypesWithConstructors
        source.theory.presentation.presentation.language allowed
        environment.sourceAtomFreeContext bound
        (arguments.map environment.reify) parameters := by
    cases typed with
    | nil => exact .nil
    | @cons _ argument arguments parameter parameters expected representation
        parameterType argumentTyped argumentsTyped =>
        have retypedArgument :=
          reifySourceHasTypeWithConstructorsAux environment argumentTyped (by
            intro name nameMembership
            apply covered name
            simp [nameMembership])
        have retypedArguments :=
          reifySourceArgumentsHaveTypesWithConstructorsAux environment
            argumentsTyped (by
              intro name nameMembership
              apply covered name
              simp [nameMembership])
        have reifiedRepresentation :
            WellSorted.MatchesParameterRepresentation parameter
              (environment.reify argument) := by
          rw [environment.reify_eq_substituteAt
            (profile := source.reflection.1)
            0 argument]
          exact WellSorted.MatchesParameterRepresentation.substituteReflectiveAt
            source.reflection.1 parameter argument
              (fun _ => [])
              environment.reificationAssignment 0 representation
        exact .cons reifiedRepresentation parameterType retypedArgument
          retypedArguments

  /-- Collection-element companion to constructor-aware atom reification. -/
  private theorem reifySourceElementsHaveTypeWithConstructorsAux
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
      {root : Pattern}
      {inventory : CostStaticParameterInventory source color targetFree table
        values root}
      (environment : CostStaticAtomEnvironment source color targetFree inventory)
      {allowed : String → Prop} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveTypeWithConstructors
        source.theory.presentation.presentation.language allowed
        table.sourceFreeContext bound elements elementType)
      (covered : ∀ name,
        name ∈ elements.flatMap Pattern.freeFvarNames →
          ∃ occurrence : CostStaticFVarOccurrence root,
            occurrence.name = name) :
      WellSorted.ElementsHaveTypeWithConstructors
        source.theory.presentation.presentation.language allowed
        environment.sourceAtomFreeContext bound
        (elements.map environment.reify) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (reifySourceHasTypeWithConstructorsAux environment elementTyped (by
            intro name nameMembership
            apply covered name
            simp [nameMembership]))
          (reifySourceElementsHaveTypeWithConstructorsAux environment
            elementsTyped (by
              intro name nameMembership
              apply covered name
              simp [nameMembership]))
end

/-- Public constructor-aware source reification law. -/
theorem reify_sourceHasTypeWithConstructors
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {allowed : String → Prop} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language allowed
      table.sourceFreeContext bound pattern type)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language allowed
      environment.sourceAtomFreeContext bound (environment.reify pattern)
      type :=
  reifySourceHasTypeWithConstructorsAux environment typed covered

/-- Restoring a reified frame is exactly evaluation by the original finite
value environment, provided every actual free-variable occurrence belongs to
the inventory root.  This is an evaluation-factorization law, not an
injectivity claim for reification. -/
theorem restoreAt_reify_eq_substituteAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (availableDepth : Nat) (pattern : Pattern)
    (covered : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence root,
        occurrence.name = name) :
    environment.restoreAt availableDepth (environment.reify pattern) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        table.restorationSupport (values.assignment table) availableDepth
        pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [restoreAt, reify, ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      obtain ⟨occurrence, occurrenceName⟩ :=
        covered name (by simp [Pattern.freeFvarNames])
      obtain ⟨slot, selectedOccurrence⟩ := Option.isSome_iff_exists.mp
        (environment.slotOfName?_isSome_of_occurrence occurrence)
      have selected : environment.slotOfName? name = some slot := by
        simpa [occurrenceName] using selectedOccurrence
      have supportEquality :
          (environment.atomValue slot).key.targetSupport =
            table.restorationSupport name := by
        simpa [occurrenceName] using
          environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
            occurrence slot selectedOccurrence
      have valueEquality :
          (environment.atomValue slot).key.normal =
            values.assignment table name := by
        simpa [occurrenceName] using
          environment.atomValue_normal_eq_of_slotOfName?_eq_some
            occurrence slot selectedOccurrence
      simp [restoreAt, reify, reifyName, selected,
        ReflectiveContextSupport.substituteAt, supportEquality, valueEquality]
  | happly constructor arguments inductionHypothesis =>
      simp only [reify, restoreAt, ReflectiveContextSupport.substituteAt,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [reify, restoreAt, ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [reify, restoreAt, ReflectiveContextSupport.substituteAt]
      congr 1
      apply inductionHypothesis
      intro name nameMembership
      apply covered name
      simpa [Pattern.freeFvarNames] using nameMembership
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [reify, restoreAt, ReflectiveContextSupport.substituteAt]
      congr 1
      · apply bodyInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
      · apply replacementInduction
        intro name nameMembership
        apply covered name
        simp [Pattern.freeFvarNames, nameMembership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, restoreAt, ReflectiveContextSupport.substituteAt,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership
      apply covered name
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨element, membership, nameMembership⟩

end CostStaticAtomEnvironment

namespace CostStaticRegionNode

/-- Mapping into the selected Cost color and reinserting ambient binders do
not change the finite free-name support of the authored source skeleton. -/
@[simp]
theorem mappedThickenedSkeleton_freeFvarNames
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    node.mappedThickenedSkeleton.1.freeFvarNames =
      node.skeleton.1.freeFvarNames := by
  simp [mappedThickenedSkeleton]

/-- Build the proof-relevant occurrence inventory and semantic quotient for
one selected static node.  The authored source skeleton is the occurrence
root; the target frame later retains the same free names exactly. -/
def buildSemanticAtomEnvironment?
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable) :
    Option (CostStaticAtomEnvironment.Packed source color targetFree
      node.boundaryTable values node.skeleton.1) :=
  CostStaticAtomEnvironment.build? node.boundaryTable values node.skeleton.1

/-- Region certification makes the semantic-atom environment builder total.
No independent namespace-completeness assumption is exposed at the node
boundary. -/
theorem buildSemanticAtomEnvironment?_isSome
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable) :
    (node.buildSemanticAtomEnvironment? values).isSome = true := by
  exact CostStaticAtomEnvironment.build?_isSome_of_typed
    node.boundaryTable values node.skeleton.2.1.1
      node.skeleton.2.1.2.2.1

/-- Deterministically recover the complete proof-relevant semantic-atom
environment for an admitted static node.  Totality comes from the node's
authored typing certificate; there is no default inventory or atom table. -/
def semanticAtomEnvironment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable) :
    CostStaticAtomEnvironment.Packed source color targetFree
      node.boundaryTable values node.skeleton.1 :=
  let result := node.buildSemanticAtomEnvironment? values
  result.get (node.buildSemanticAtomEnvironment?_isSome values)

/-- The total semantic environment is exactly the successful result of the
finite executable builder. -/
theorem buildSemanticAtomEnvironment?_eq_some_semanticAtomEnvironment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable) :
    node.buildSemanticAtomEnvironment? values =
      some (node.semanticAtomEnvironment values) := by
  exact (Option.some_get
    (node.buildSemanticAtomEnvironment?_isSome values)).symm

/-- The total builder's environment projection is the canonical quotient of
its retained positional inventory.  Exposing this equality once keeps later
dependent transports independent of the `Option.get` proof used for totality. -/
theorem semanticAtomEnvironment_snd_eq_ofInventory_fst
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable) :
    (node.semanticAtomEnvironment values).2 =
      CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1 := by
  generalize packedEq : node.semanticAtomEnvironment values = packed
  rcases packed with ⟨inventory, environment⟩
  change environment = CostStaticAtomEnvironment.ofInventory inventory
  have built :=
    node.buildSemanticAtomEnvironment?_eq_some_semanticAtomEnvironment values
  rw [packedEq] at built
  unfold buildSemanticAtomEnvironment? CostStaticAtomEnvironment.build? at built
  cases builtEq : CostStaticParameterInventory.build? node.boundaryTable values
      node.skeleton.1 with
  | none =>
      simp [builtEq] at built
  | some inventory =>
      simp only [builtEq] at built
      have packedEq := Option.some.inj built
      cases packedEq
      rfl

/-- Every free name used by the selected authored skeleton has a positional
occurrence in the semantic inventory root. -/
theorem skeleton_fvar_covered
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (name : String) (membership : name ∈ node.skeleton.1.freeFvarNames) :
    ∃ occurrence : CostStaticFVarOccurrence node.skeleton.1,
      occurrence.name = name :=
  CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object membership
    node.skeleton.2.1.2.2.1

/-- The authored skeleton with each finite external parameter replaced by
its semantic atom.  This remains an object of the original authored theory;
the Cost symbol map has not acted yet. -/
def reifiedSourceFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ReflectiveWellSorted.OpenTerm source.reflection.1
      source.theory.presentation.presentation.language
      environment.sourceAtomFreeContext node.sourceBound node.sourceSort := by
  let supported := environment.reify_sourceHasTypeWithConstructors
    node.supported node.skeleton_fvar_covered
  let core : WellSorted.OpenTerm
      source.theory.presentation.presentation.language
      environment.sourceAtomFreeContext node.sourceBound node.sourceSort := by
    refine ⟨environment.reify node.skeleton.1, supported.toHasType,
      ?_, ?_, supported.toHasType.isWellScopedAt⟩
    · rw [environment.hasCanonicalBinderMetadata_reify]
      exact node.skeleton.2.1.2.1
    · rw [environment.isObjectPattern_reify]
      exact node.skeleton.2.1.2.2.1
  refine ⟨core.1, core.2, ?_⟩
  intro declaration membership
  rw [environment.binderSafeAt_reify]
  exact node.skeleton.2.2 declaration membership

@[simp]
theorem reifiedSourceFrame_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    (node.reifiedSourceFrame environment).1 =
      environment.reify node.skeleton.1 := by
  rfl

/-- The reified authored frame retains the exact generated support suffix
associated with each semantic atom. -/
theorem reifiedSourceFrame_supportSafe
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    (node.reifiedSourceFrame environment).2.1.1.ReflectiveSupportSafeAt
      source.reflection.1
      environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols source)) := by
  obtain ⟨_retyped, safe⟩ :=
    environment.reify_sourceReflectiveSupportSafeAt node.supportSafe
      node.skeleton_fvar_covered
  let supported := environment.reify_sourceHasTypeWithConstructors
    node.supported node.skeleton_fvar_covered
  have aligned : supported.toHasType.ReflectiveSupportSafeAt
      source.reflection.1
      environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols source)) := safe.castTyping
  exact aligned

/-- Constructor-fragment evidence for the reified authored frame.  In
particular, proof-relevant bare-collection choices are preserved exactly. -/
theorem reifiedSourceFrame_supported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      environment.sourceAtomFreeContext node.sourceBound
      (node.reifiedSourceFrame environment).1 (.base node.sourceSort.1) := by
  simpa only [node.reifiedSourceFrame_pattern] using
    (environment.reify_sourceHasTypeWithConstructors node.supported
      node.skeleton_fvar_covered)

/-- Proof-relevant authored carrier used to relate atomized target-frame
steps back to the sole source equation theory.  Exact hereditary ordering is
performed on the selected target frame with a semantic key below. -/
def reifiedSourceTerm
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    CostStaticSourceTerm source color environment.sourceAtomFreeContext
      environment.sourceAtomSupport node.sourceBound node.targetBound
      node.sourceSort where
  term := node.reifiedSourceFrame environment
  supported := node.reifiedSourceFrame_supported environment
  safe := node.reifiedSourceFrame_supportSafe environment

/-- Every semantic slot in the canonical quotient inherits the certified
source-to-target type map of the selected static plan. -/
theorem semanticAtom_typeMap
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    mapTypeExpr (color.symbols source)
        ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.sourceType =
      ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.targetType :=
  CostStaticAtomEnvironment.ofInventory_atomValue_targetType_eq_map_sourceType
    inventory node.plan.boundaryTable_fiberCoherent slot

/-- Replace the finite rigid parameters of the selected target frame by
canonical semantic-atom names. -/
def reifyTargetFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    Pattern :=
  environment.reify node.mappedThickenedSkeleton.1

/-- The atomized generated frame is exactly the Cost image of the atomized
authored frame, followed by the node's certified ambient-binder insertion.
This is the local naturality square relating the semantic-atom carrier to the
generated static fibre. -/
theorem reifyTargetFrame_eq_map_reifiedSourceFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    node.reifyTargetFrame environment =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols source)
          (node.reifiedSourceFrame environment).1) := by
  simp [reifyTargetFrame, mappedThickenedSkeleton,
    reifiedSourceFrame_pattern]

/-- The source target-frame carrier restricted to exactly the finite names it
uses.  Restriction avoids granting unused ambient context entries any role in
semantic-atom reification. -/
def restrictedTargetFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage
      (node.boundaryTable.mappedFreeContext.restrictTo
        node.mappedThickenedSkeleton.1.freeFvarNames)
      node.targetBound (color.mapLangSort source node.sourceSort) :=
  node.mappedThickenedReflectiveSkeleton.restrictFreeContext

/-- Atom reification as a typed open assignment on the exact finite source
context of one frame.  Each used original name is resolved through a genuine
positional occurrence; its atom type is therefore inherited from the same
finite table that typed the frame. -/
def reificationSupportedOpenAssignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    WellSorted.SupportedOpenAssignment source.costWholeReflectionProfile
      source.costWholeLanguage
      (node.boundaryTable.mappedFreeContext.restrictTo
        node.mappedThickenedSkeleton.1.freeFvarNames)
      environment.atomFreeContext (fun _ => []) where
  assignment := environment.reificationAssignment
  typed := by
    intro name type lookup
    have membership : name ∈
        node.mappedThickenedSkeleton.1.freeFvarNames :=
      WellSorted.FreeTypeContext.mem_of_restrictTo_eq_some lookup
    have mappedLookup :
        node.boundaryTable.mappedFreeContext name = some type := by
      rw [WellSorted.FreeTypeContext.restrictTo_apply_of_mem
        node.boundaryTable.mappedFreeContext
        node.mappedThickenedSkeleton.1.freeFvarNames name membership] at lookup
      exact lookup
    have sourceMembership : name ∈ node.skeleton.1.freeFvarNames := by
      simpa using membership
    obtain ⟨occurrence, occurrenceName⟩ :=
      CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
        sourceMembership node.skeleton.2.1.2.2.1
    obtain ⟨slot, selectedOccurrence⟩ := Option.isSome_iff_exists.mp
      (environment.slotOfName?_isSome_of_occurrence occurrence)
    have selected : environment.slotOfName? name = some slot := by
      simpa [occurrenceName] using selectedOccurrence
    have atomTypeLookup :=
      environment.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
        occurrence slot selectedOccurrence
    have atomTypeLookupAtName :
        node.boundaryTable.mappedFreeContext name =
          some (environment.atomValue slot).key.targetType := by
      simpa [occurrenceName] using atomTypeLookup
    have typeEquality :
        (environment.atomValue slot).key.targetType = type :=
      Option.some.inj (atomTypeLookupAtName.symm.trans mappedLookup)
    have atomLookup : environment.atomFreeContext
        (environment.atomName slot) = some type := by
      rw [environment.atomFreeContext_atomName, typeEquality]
    simpa [CostStaticAtomEnvironment.reificationAssignment,
      CostStaticAtomEnvironment.reifyName, selected] using
      (WellSorted.HasType.fvar (bound := []) atomLookup)
  canonicalBinderMetadata := by
    intro name type lookup
    simp [CostStaticAtomEnvironment.reificationAssignment,
      CostStaticAtomEnvironment.reifyName,
      Pattern.hasCanonicalBinderMetadata]
  objectPattern := by
    intro name type lookup
    simp [CostStaticAtomEnvironment.reificationAssignment,
      CostStaticAtomEnvironment.reifyName, WellSorted.isObjectPattern]
  reflectiveScopeSafe := by
    intro name type lookup presentation membership
    simp [CostStaticAtomEnvironment.reificationAssignment,
      CostStaticAtomEnvironment.reifyName, binderSafeAt]

/-- The atomized target frame is a genuine open object in the same generated
Cost language and sort.  Its sole free context is the finite semantic-atom
context; no raw pattern rechecking or second typing authority is used. -/
def reifiedTargetFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage environment.atomFreeContext
      node.targetBound (color.mapLangSort source node.sourceSort) := by
  let restricted := node.restrictedTargetFrame
  let assignment := node.reificationSupportedOpenAssignment environment
  let safe := restricted.2.1.1.reflectiveSupportSafeAt_empty
    (profile := source.costWholeReflectionProfile) node.targetBound
  let substituted :=
    WellSorted.ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported
      restricted assignment safe
  have patternEquality : substituted.1 = node.reifyTargetFrame environment := by
    change ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile
        (fun _ => []) environment.reificationAssignment
          node.targetBound.length node.mappedThickenedSkeleton.1 =
      environment.reify node.mappedThickenedSkeleton.1
    exact (environment.reify_eq_substituteAt
      (profile := source.costWholeReflectionProfile) node.targetBound.length
      node.mappedThickenedSkeleton.1).symm
  refine ⟨node.reifyTargetFrame environment, ?_⟩
  rw [← patternEquality]
  exact substituted.2

@[simp]
theorem reifiedTargetFrame_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    (node.reifiedTargetFrame environment).1 =
      node.reifyTargetFrame environment := by
  rfl

/-- Every constructor retained in an atomized target frame belongs to the
single static Cost namespace selected by the region plan.  Foreign-colour
static subtrees have already become semantic atoms, while binder insertion and
atom-name reification preserve constructor labels. -/
theorem reifiedTargetFrame_constructorsWithinColor
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (node.reifiedTargetFrame environment).1 := by
  have mapped : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (mapPattern (color.symbols source)
        (node.reifiedSourceFrame environment).1) := by
    apply constructorsWithin_mapPattern (color.symbols source)
    · intro constructor _membership
      exact ⟨constructor,
        decodeCostStaticConstructor_symbols source color constructor⟩
    · exact (node.reifiedSourceFrame_supported environment).constructorsWithin
  rw [node.reifiedTargetFrame_pattern,
    node.reifyTargetFrame_eq_map_reifiedSourceFrame environment]
  exact node.thinning.constructorsWithin_thickenAmbientBVars mapped 0

/-- Every free name in the atomized target frame resolves to its finite
semantic-atom slot.  The proof reads the frame's typed open carrier; it does
not rescan or reclassify the raw syntax. -/
theorem reifyTargetFrame_atomCovered
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (name : String) (membership : name ∈
      (node.reifyTargetFrame environment).freeFvarNames) :
    exists slot, environment.lookupAtom? name = some slot := by
  let term := node.reifiedTargetFrame environment
  have termMembership : name ∈ term.1.freeFvarNames := by
    simpa only [term, node.reifiedTargetFrame_pattern] using membership
  obtain ⟨type, lookup⟩ :=
    term.toCore.freeType_of_mem_freeFvarNames termMembership
  change environment.atomFreeContext name = some type at lookup
  simp only [CostStaticAtomEnvironment.atomFreeContext] at lookup
  cases selected : environment.lookupAtom? name with
  | none => simp [selected] at lookup
  | some slot => exact ⟨slot, rfl⟩

/-- The atomized target frame retains the exact reflective support assigned
to every semantic atom.  This is stronger than ordinary well-sortedness and
is the certificate required before a selected reflective canonicalizer may
move, flatten, or quote parts of the frame. -/
theorem reifiedTargetFrame_supportSafe
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    (node.reifiedTargetFrame environment).2.1.1.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile
      environment.restorationSupport node.targetBound := by
  obtain ⟨retyped, safe⟩ := environment.reify_reflectiveSupportSafeAt
    node.mappedThickenedSkeleton_supportSafe (by
      intro name membership
      have sourceMembership : name ∈ node.skeleton.1.freeFvarNames := by
        simpa using membership
      exact CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
        sourceMembership node.skeleton.2.1.2.2.1)
  simpa only [node.reifiedTargetFrame_pattern, reifyTargetFrame] using
    safe.castTyping

/-- Local exactness of semantic-atom reification.  Restoring the atomized
target frame agrees definitionally with the established finite-value
evaluation of the original target frame.  Coalesced origins remain distinct
as occurrences in `inventory`, although their reified names may coincide. -/
theorem restore_reifyTargetFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    environment.restore node.targetBound
        (node.reifyTargetFrame environment) =
      values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1 := by
  have factor := environment.restoreAt_reify_eq_substituteAt
    node.targetBound.length node.mappedThickenedSkeleton.1 (by
      intro name membership
      have sourceMembership : name ∈ node.skeleton.1.freeFvarNames := by
        simpa using membership
      exact CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
        sourceMembership node.skeleton.2.1.2.2.1)
  simpa [CostStaticAtomEnvironment.restore,
    reifyTargetFrame,
    TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute] using factor

/-- Ordering key for one atomized target subframe.  It evaluates opaque atoms
only for comparison, at the quote-visible binder depth supplied by the keyed
canonicalizer; the returned frame itself still contains the atoms. -/
def semanticPatternKeyAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (availableDepth : Nat) (pattern : Pattern) : Nat :=
  Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
    (environment.restoreAt availableDepth pattern)

/-- Canonicalize only the selected target-color frame.  Normalized foreign
children remain opaque atoms during traversal, while their restored semantic
values determine the order of parallel components. -/
def canonicalizeReifiedTargetFrame
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (declaration : ReflectivePresentationDecl) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
    (semanticPatternKeyAt environment) declaration node.targetBound.length
      (node.reifyTargetFrame environment)

/-- Keyed ordering chooses an exact representative inside the authored
reflective equation class of the atomized target frame.  The key contributes
only an order; validation ties every structural move back to the selected
language declaration. -/
theorem canonicalizeReifiedTargetFrame_equationEquiv
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.costWholeReflectionProfile.presentations) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage
      (node.canonicalizeReifiedTargetFrame environment declaration)
      (node.reifyTargetFrame environment) := by
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      source.costWholeAdmittedReflection.2 membership
  have quote_ne_drop :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
      source.costWholeLanguage declaration declarationValid
  apply Relation.EqvGen.rel
  apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext
    .hole membership
  simpa only [reifyTargetFrame] using
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_canonicalizeByAt
      (semanticPatternKeyAt environment) declaration quote_ne_drop
      node.targetBound.length (node.reifyTargetFrame environment)

/-- Raw hereditary factorization for one explicit finite occurrence
inventory.  Typing and equation soundness are established separately for a
selected declaration; the definition itself contains no fallback. -/
def normalizeHereditaryRawWithInventory
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (declaration : ReflectivePresentationDecl) : Pattern :=
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  environment.restore node.targetBound
    (node.canonicalizeReifiedTargetFrame environment declaration)

/-- Executable finite-builder boundary of hereditary frame normalization. -/
def normalizeHereditaryRaw?
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable)
    (declaration : ReflectivePresentationDecl) : Option Pattern :=
  match CostStaticParameterInventory.build? node.boundaryTable values
      node.skeleton.1 with
  | none => none
  | some inventory =>
      some (node.normalizeHereditaryRawWithInventory values inventory
        declaration)

/-- Occurrence classification makes the raw hereditary builder total for
every certified static node and every selected reflective declaration. -/
theorem normalizeHereditaryRaw?_isSome
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable)
    (declaration : ReflectivePresentationDecl) :
    (node.normalizeHereditaryRaw? values declaration).isSome = true := by
  have inventoryTotal := CostStaticParameterInventory.build?_isSome_of_typed
    node.boundaryTable values node.skeleton.2.1.1
      node.skeleton.2.1.2.2.1
  unfold normalizeHereditaryRaw?
  cases built : CostStaticParameterInventory.build? node.boundaryTable values
      node.skeleton.1 with
  | none => simp [built] at inventoryTotal
  | some inventory => simp

end CostStaticRegionNode

end Mettapedia.GSLT.LanguageDef
