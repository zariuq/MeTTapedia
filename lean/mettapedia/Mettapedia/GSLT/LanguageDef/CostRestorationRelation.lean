import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Depth-uniform restoration equality

Hereditary Cost normalization compares semantic leaves below binders and
reflective quotations.  Equality at one ambient depth is therefore not a
stable induction hypothesis.  `RestoresTogether` records equality after the
same supported assignment at every depth and supplies the structural closure
rules needed by recursive common-apex constructions.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ReflectiveContextSupport

/-- Two compact patterns restore to the same pattern at every ambient binder
depth under one profile, support function, and assignment. -/
def RestoresTogether (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (left right : Pattern) : Prop :=
  ∀ depth,
    substituteAt profile support assignment depth left =
      substituteAt profile support assignment depth right

namespace RestoresTogether

theorem refl (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (pattern : Pattern) :
    RestoresTogether profile support assignment pattern pattern := by
  intro depth
  rfl

theorem symm {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {left right : Pattern}
    (restores : RestoresTogether profile support assignment left right) :
    RestoresTogether profile support assignment right left := by
  intro depth
  exact (restores depth).symm

theorem trans {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {first second third : Pattern}
    (firstSecond : RestoresTogether profile support assignment first second)
    (secondThird : RestoresTogether profile support assignment second third) :
    RestoresTogether profile support assignment first third := by
  intro depth
  exact (firstSecond depth).trans (secondThird depth)

private theorem map_substituteAt_eq_of_forall₂
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {left right : List Pattern}
    (related : List.Forall₂
      (RestoresTogether profile support assignment) left right)
    (depth : Nat) :
    left.map (substituteAt profile support assignment depth) =
      right.map (substituteAt profile support assignment depth) := by
  induction related with
  | nil => rfl
  | cons headRestores tailRestores inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headRestores depth, inductionHypothesis⟩

theorem apply {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {constructor : String}
    {leftArguments rightArguments : List Pattern}
    (arguments : List.Forall₂
      (RestoresTogether profile support assignment)
      leftArguments rightArguments) :
    RestoresTogether profile support assignment
      (.apply constructor leftArguments) (.apply constructor rightArguments) := by
  intro depth
  simp only [substituteAt, Pattern.apply.injEq, true_and]
  exact map_substituteAt_eq_of_forall₂ arguments
    (if isQuoteConstructor profile constructor then 0 else depth)

theorem lambda {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {binder : Option String}
    {leftBody rightBody : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody) :
    RestoresTogether profile support assignment
      (.lambda binder leftBody) (.lambda binder rightBody) := by
  intro depth
  simp only [substituteAt, Pattern.lambda.injEq, true_and]
  exact body (depth + 1)

theorem multiLambda {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {arity : Nat}
    {binders : List String} {leftBody rightBody : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody) :
    RestoresTogether profile support assignment
      (.multiLambda arity binders leftBody)
      (.multiLambda arity binders rightBody) := by
  intro depth
  simp only [substituteAt, Pattern.multiLambda.injEq, true_and]
  exact body (depth + arity)

theorem subst {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {leftBody rightBody leftReplacement rightReplacement : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody)
    (replacement : RestoresTogether profile support assignment
      leftReplacement rightReplacement) :
    RestoresTogether profile support assignment
      (.subst leftBody leftReplacement) (.subst rightBody rightReplacement) := by
  intro depth
  simp only [substituteAt, Pattern.subst.injEq]
  exact ⟨body (depth + 1), replacement depth⟩

theorem collection {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    (elements : List.Forall₂
      (RestoresTogether profile support assignment)
      leftElements rightElements) :
    RestoresTogether profile support assignment
      (.collection collectionType leftElements rest)
      (.collection collectionType rightElements rest) := by
  intro depth
  simp only [substituteAt]
  rw [map_substituteAt_eq_of_forall₂ elements depth]

/-- A bound variable is a rigid restoration leaf: supported substitution
never consults the assignment at that node. -/
theorem bvar (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (index : Nat) :
    RestoresTogether profile support assignment (.bvar index) (.bvar index) :=
  refl profile support assignment (.bvar index)

/-- Two parameter names with one closed assigned value restore together even
when their declared support suffixes differ.  Closedness is exactly what
makes both support-indexed weakenings inert. -/
theorem fvar_of_assignment_eq_of_scoped
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (leftName rightName : String)
    (assignmentEq : assignment leftName = assignment rightName)
    (assignedScoped : (assignment leftName).isWellScopedAt 0 = true) :
    RestoresTogether profile support assignment
      (.fvar leftName) (.fvar rightName) := by
  intro depth
  simp only [substituteAt]
  rw [assignmentEq]
  have rightScoped : (assignment rightName).isWellScopedAt 0 = true := by
    simpa only [assignmentEq] using assignedScoped
  rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped]

/-- The closed-value premise of `fvar_of_assignment_eq_of_scoped` cannot be
dropped.  With one retained binder on the left and none on the right, assigning
the same bound variable produces different de Bruijn indices at depth one. -/
theorem unequal_support_bvar_assignment_not_restoresTogether
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (binderType : TypeExpr) :
    let support : ContextSupport.Support := fun name =>
      if name = "left" then [binderType] else []
    let assignment : ContextSupport.Assignment := fun _ => .bvar 0
    ¬ RestoresTogether profile support assignment
      (.fvar "left") (.fvar "right") := by
  dsimp only
  intro restores
  have atDepthOne := restores 1
  simp [substituteAt, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at atDepthOne

mutual
  /-- A structural semantic-leaf alignment whose selected leaves restore
  together itself restores together at every depth. -/
  def PatternLeafAligned.toRestoresTogether
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
      {assignment : ContextSupport.Assignment} :
      ∀ {left right : Pattern},
        PatternLeafAligned
          (RestoresTogether profile support assignment) left right →
        RestoresTogether profile support assignment left right
    | _, _, .leaf related => related
    | _, _, .bvar index =>
        RestoresTogether.bvar profile support assignment index
    | _, _, .apply constructor arguments =>
        RestoresTogether.apply
          (PatternLeafAlignedList.toRestoresTogether arguments)
    | _, _, .lambda binder body =>
        RestoresTogether.lambda
          (PatternLeafAligned.toRestoresTogether body)
    | _, _, .multiLambda arity binders body =>
        RestoresTogether.multiLambda
          (PatternLeafAligned.toRestoresTogether body)
    | _, _, .subst body replacement =>
        RestoresTogether.subst
          (PatternLeafAligned.toRestoresTogether body)
          (PatternLeafAligned.toRestoresTogether replacement)
    | _, _, .collection collectionType rest elements =>
        RestoresTogether.collection
          (PatternLeafAlignedList.toRestoresTogether elements)

  /-- Listwise companion of `PatternLeafAligned.toRestoresTogether`. -/
  def PatternLeafAlignedList.toRestoresTogether
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
      {assignment : ContextSupport.Assignment} :
      ∀ {left right : List Pattern},
        PatternLeafAlignedList
          (RestoresTogether profile support assignment) left right →
        List.Forall₂ (RestoresTogether profile support assignment) left right
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (PatternLeafAligned.toRestoresTogether head)
          (PatternLeafAlignedList.toRestoresTogether tail)
end

end RestoresTogether

end ReflectiveContextSupport

/-! ## Recursive common restoration apex

Pointwise leaf alignment is insufficient for canonical parallel frames: two
stable sorts may retain different orders among semantically equal keys.  A
single top-level permutation is also insufficient because a parallel frame
may occur below an ordinary constructor or binder.  The following family is
the congruence generated by depth-uniform leaf restoration and restored
parallel permutation.

Its endpoints live in the common namespace of a semantic-key cospan.  This is
important: occurrence and boundary identities remain in the endpoint
environments, while the relation compares only the meanings transported to
their common apex.
-/

namespace CostStaticAtomKeyCospan

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Binder depth visible at the hole of a one-hole context.

Ordinary application and collection frames preserve depth, binders extend
it, and reflective quote constructors reset it.  This is the unique depth
index at which an apex for the hole may be lifted back through the context. -/
def restorationDepthThroughContext (source : CIGSLT) :
    Nat → OneHoleContext → Nat
  | depth, .hole => depth
  | depth, .apply constructor _ inner _ =>
      restorationDepthThroughContext source
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        inner
  | depth, .lambda _ inner =>
      restorationDepthThroughContext source (depth + 1) inner
  | depth, .multiLambda arity _ inner =>
      restorationDepthThroughContext source (depth + arity) inner
  | depth, .substBody inner _ =>
      restorationDepthThroughContext source (depth + 1) inner
  | depth, .substReplacement _ inner =>
      restorationDepthThroughContext source depth inner
  | depth, .collection _ _ inner _ _ =>
      restorationDepthThroughContext source depth inner

/-- The depth index used by common-restoration contexts is exactly the depth
computed by operational reflective substitution.  The support and assignment
can change the transported fixed syntax, but cannot change the quotation and
binder path leading to the hole. -/
@[simp]
theorem restorationDepthThroughContext_eq_substituteContextAt_snd
    (source : CIGSLT) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (depth : Nat)
    (context : OneHoleContext) :
    restorationDepthThroughContext source depth context =
      (ReflectiveContextSupport.substituteContextAt
        source.costWholeReflectionProfile support assignment depth context).2 := by
  induction context generalizing depth with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _
  | lambda binder inner inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _
  | substBody inner replacement inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _
  | substReplacement body inner inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [restorationDepthThroughContext,
        ReflectiveContextSupport.substituteContextAt]
      exact inductionHypothesis _

/-- Reify every fixed pattern of a one-hole context through one endpoint leg.
The hole itself remains distinguished, so an independently reified selected
occurrence can be inserted afterwards. -/
def reifyContextWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length) :
    OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor (before.map (cospan.reifyWith resolve leg))
        (reifyContextWith cospan resolve leg inner)
        (after.map (cospan.reifyWith resolve leg))
  | .lambda binder inner =>
      .lambda binder (reifyContextWith cospan resolve leg inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity binders
        (reifyContextWith cospan resolve leg inner)
  | .substBody inner replacement =>
      .substBody (reifyContextWith cospan resolve leg inner)
        (cospan.reifyWith resolve leg replacement)
  | .substReplacement body inner =>
      .substReplacement (cospan.reifyWith resolve leg body)
        (reifyContextWith cospan resolve leg inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType (before.map (cospan.reifyWith resolve leg))
        (reifyContextWith cospan resolve leg inner)
        (after.map (cospan.reifyWith resolve leg)) rest

/-- Context reification commutes with filling its unique occurrence. -/
theorem reifyContextWith_fill
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (context : OneHoleContext) (pattern : Pattern) :
    (reifyContextWith cospan resolve leg context).fill
        (cospan.reifyWith resolve leg pattern) =
      cospan.reifyWith resolve leg (context.fill pattern) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, List.map_append,
        inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [reifyContextWith, OneHoleContext.fill,
        CostStaticAtomKeyCospan.reifyWith, List.map_append,
        inductionHypothesis]

/-- The free-variable spelling selected by one endpoint-to-common cospan
leg.  This is the name-level component of `reifyWith`; keeping it explicit
allows an occurrence zipper to be transported without recovering its leaf
from the reified term by equality search. -/
def reifyNameWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (name : String) : String :=
  match resolve name with
  | some slot => cospan.commonAtomName (leg slot)
  | none => name

@[simp]
theorem reifyWith_fvar
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (name : String) :
    cospan.reifyWith resolve leg (.fvar name) =
      .fvar (cospan.reifyNameWith resolve leg name) := by
  cases selected : resolve name <;>
    simp [CostStaticAtomKeyCospan.reifyWith, reifyNameWith, selected]

/-- Transport one exact free-variable occurrence through a chosen common-key
leg.  The selected leaf is renamed, while the complete one-hole zipper is
mapped structurally and remains proof-relevant. -/
noncomputable def reifyOccurrenceWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root) :
    CostStaticFVarOccurrence (cospan.reifyWith resolve leg root) :=
  { name := cospan.reifyNameWith resolve leg occurrence.name
    context := cospan.reifyContextWith resolve leg occurrence.context
    selected := by
      have filled :
          (cospan.reifyContextWith resolve leg occurrence.context).fill
              (.fvar (cospan.reifyNameWith resolve leg occurrence.name)) =
            cospan.reifyWith resolve leg root := by
        calc
          (cospan.reifyContextWith resolve leg occurrence.context).fill
                (.fvar (cospan.reifyNameWith resolve leg occurrence.name)) =
              (cospan.reifyContextWith resolve leg occurrence.context).fill
                (cospan.reifyWith resolve leg
                  (.fvar occurrence.name)) := by
            rw [cospan.reifyWith_fvar]
          _ = cospan.reifyWith resolve leg
                (occurrence.context.fill (.fvar occurrence.name)) :=
            cospan.reifyContextWith_fill resolve leg occurrence.context
              (.fvar occurrence.name)
          _ = cospan.reifyWith resolve leg root :=
            congrArg (cospan.reifyWith resolve leg)
              occurrence.selected.fill_eq
      rw [← filled]
      exact Selects.of_fill
        (cospan.reifyContextWith resolve leg occurrence.context)
        (.fvar (cospan.reifyNameWith resolve leg occurrence.name)) }

@[simp]
theorem reifyOccurrenceWith_name
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root) :
    (cospan.reifyOccurrenceWith resolve leg occurrence).name =
      cospan.reifyNameWith resolve leg occurrence.name := rfl

@[simp]
theorem reifyOccurrenceWith_context
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    {root : Pattern} (occurrence : CostStaticFVarOccurrence root) :
    (cospan.reifyOccurrenceWith resolve leg occurrence).context =
      cospan.reifyContextWith resolve leg occurrence.context := rfl

/-- Reify a source-level context through its endpoint semantic-atom
environment and then through one leg of a common semantic-key cospan.

The two stages are intentionally explicit.  The environment identifies the
frame's original rigid-parameter names with its proof-relevant atom slots;
the cospan then changes only those internal atom names into the common
comparison namespace. -/
def reifyEnvironmentContext
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (context : OneHoleContext) : OneHoleContext :=
  cospan.reifyContextWith environment.lookupAtom? leg
    (environment.reifyContext context)

/-- Two-stage context reification commutes with filling.  In particular, a
selected occurrence and the fixed frame around it cannot be transported by
different naming conventions. -/
theorem reifyEnvironmentContext_fill
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (context : OneHoleContext) (pattern : Pattern) :
    (cospan.reifyEnvironmentContext environment leg context).fill
        (cospan.reifyWith environment.lookupAtom? leg
          (environment.reify pattern)) =
      cospan.reifyWith environment.lookupAtom? leg
        (environment.reify (context.fill pattern)) := by
  rw [reifyEnvironmentContext, cospan.reifyContextWith_fill,
    environment.reifyContext_fill]

/-- Carry one endpoint occurrence through both naming stages used by common
restoration: first into the endpoint semantic-atom namespace, then through
the chosen cospan leg.  Neither stage searches for the occurrence again. -/
noncomputable def reifyEnvironmentOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (occurrence : CostStaticFVarOccurrence root) :
    CostStaticFVarOccurrence
      (cospan.reifyWith environment.lookupAtom? leg
        (environment.reify root)) :=
  cospan.reifyOccurrenceWith environment.lookupAtom? leg
    (environment.reifyOccurrence occurrence)

@[simp]
theorem reifyEnvironmentOccurrence_context
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (occurrence : CostStaticFVarOccurrence root) :
    (cospan.reifyEnvironmentOccurrence environment leg occurrence).context =
      cospan.reifyEnvironmentContext environment leg occurrence.context := rfl

/-- A source occurrence selected by endpoint slot `slot` becomes exactly the
common atom name at `leg slot`.  This is the point at which positional cause
may be projected to a semantic key; the occurrence zipper itself is retained
by `reifyEnvironmentOccurrence`. -/
theorem reifyEnvironmentOccurrence_name_eq_commonAtomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (cospan.reifyEnvironmentOccurrence environment leg occurrence).name =
      cospan.commonAtomName (leg slot) := by
  simp only [reifyEnvironmentOccurrence, reifyOccurrenceWith_name,
    CostStaticAtomEnvironment.reifyOccurrence_name]
  have reifiedName : environment.reifyName occurrence.name =
      environment.atomName slot := by
    simp [CostStaticAtomEnvironment.reifyName, selected]
  rw [reifiedName]
  simp [reifyNameWith, environment.lookupAtom?_atomName]

/- Recursive equality evidence at a common semantic restoration apex.

The depth index is proof-relevant.  Ordinary binders increase it, reflective
quotes reset it, and a parallel node uses it both for semantic keying and for
the final supported restoration. -/
mutual
inductive CommonRestorationApex
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Pattern → Pattern → Prop where
  /-- Structural alignment outside leaves which already restore together at
  every possible depth. -/
  | leafAligned {depth : Nat} {left right : Pattern}
      (aligned : PatternLeafAligned
        (ReflectiveContextSupport.RestoresTogether
          source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment) left right) :
      CommonRestorationApex source cospan declaration depth left right
  /-- Rigid ordinary application congruence.  Quote applications use depth
  zero for every argument; other constructors preserve the current depth. -/
  | apply {depth : Nat} (constructor : String)
      {leftArguments rightArguments : List Pattern}
      (arguments : CommonRestorationApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        leftArguments rightArguments) :
      CommonRestorationApex source cospan declaration depth
        (.apply constructor leftArguments) (.apply constructor rightArguments)
  | lambda {depth : Nat} (binder : Option String)
      {leftBody rightBody : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + 1)
        leftBody rightBody) :
      CommonRestorationApex source cospan declaration depth
        (.lambda binder leftBody) (.lambda binder rightBody)
  | multiLambda {depth arity : Nat} (binders : List String)
      {leftBody rightBody : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + arity)
        leftBody rightBody) :
      CommonRestorationApex source cospan declaration depth
        (.multiLambda arity binders leftBody)
        (.multiLambda arity binders rightBody)
  | subst {depth : Nat}
      {leftBody rightBody leftReplacement rightReplacement : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + 1)
        leftBody rightBody)
      (replacement : CommonRestorationApex source cospan declaration depth
        leftReplacement rightReplacement) :
      CommonRestorationApex source cospan declaration depth
        (.subst leftBody leftReplacement)
        (.subst rightBody rightReplacement)
  | collection {depth : Nat} (collectionType : CollType)
      (rest : Option String) {leftElements rightElements : List Pattern}
      (elements : CommonRestorationApexList source cospan declaration depth
        leftElements rightElements) :
      CommonRestorationApex source cospan declaration depth
        (.collection collectionType leftElements rest)
        (.collection collectionType rightElements rest)
  /-- Bare parallel canonicalization retains recursive evidence for every
  frontier occurrence before a final finite reordering.  The intermediate
  list separates semantic alignment from scheduling order, so duplicate
  occurrences remain distinct and no stable-tie order becomes semantics. -/
  | parallel {depth : Nat} {leftElements rightElements middle : List Pattern}
      (aligned : CommonRestorationApexList source cospan declaration depth
        (parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration depth
            leftElements))
        middle)
      (permutation : List.Perm middle
        (parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration depth
            rightElements))) :
      CommonRestorationApex source cospan declaration depth
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth
          (.collection declaration.parallelCollection leftElements none))
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth
          (.collection declaration.parallelCollection rightElements none))

/-- Pointwise companion used by rigid application and collection
congruence. -/
inductive CommonRestorationApexList
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → List Pattern → List Pattern → Prop where
  | nil (depth : Nat) :
      CommonRestorationApexList source cospan declaration depth [] []
  | cons {depth : Nat} {leftHead rightHead : Pattern}
      {leftTail rightTail : List Pattern}
      (head : CommonRestorationApex source cospan declaration depth
        leftHead rightHead)
      (tail : CommonRestorationApexList source cospan declaration depth
        leftTail rightTail) :
      CommonRestorationApexList source cospan declaration depth
        (leftHead :: leftTail) (rightHead :: rightTail)
end

namespace CommonRestorationApex

/-- Reflexive apex evidence.  Free variables use the depth-uniform reflexive
restoration law; all rigid structure is retained by `PatternLeafAligned`. -/
theorem refl
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (pattern : Pattern) :
    CommonRestorationApex source cospan declaration depth pattern pattern :=
  .leafAligned (PatternLeafAligned.refl
    (fun name => ReflectiveContextSupport.RestoresTogether.refl
      source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment
      (.fvar name)) pattern)

/-- Exact equality embeds into the restoration relation without inventing a
semantic leaf or a permutation. -/
theorem of_eq
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : Pattern} (equal : left = right) :
    CommonRestorationApex source cospan declaration depth left right := by
  subst right
  exact refl cospan declaration depth left

/-- Depth-uniform equality of the collision-free semantic key is sufficient
for a semantic-leaf apex.  This is the intended way stable key ties enter the
relation: the tie certifies equal restored meanings, not equal provenance or
raw spelling. -/
theorem leaf_of_key_eq
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : Pattern}
    (keysEqual : ∀ currentDepth,
      cospan.commonSemanticPatternKeyAt source currentDepth left =
        cospan.commonSemanticPatternKeyAt source currentDepth right) :
    CommonRestorationApex source cospan declaration depth left right :=
  .leafAligned (.leaf (fun currentDepth =>
    (cospan.commonSemanticPatternKeyAt_eq_iff source currentDepth left right).mp
      (keysEqual currentDepth)))

/-- Pointwise reflexive evidence for an occurrence list. -/
def reflList
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    ∀ patterns : List Pattern,
      CommonRestorationApexList source cospan declaration depth patterns patterns
  | [] => .nil depth
  | pattern :: patterns =>
      .cons (refl cospan declaration depth pattern)
        (reflList cospan declaration depth patterns)

/-- Concatenate two pointwise apex lists without changing occurrence order. -/
def appendList
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) {depth : Nat} :
    ∀ {leftPrefix rightPrefix leftSuffix rightSuffix : List Pattern},
      CommonRestorationApexList source cospan declaration depth
          leftPrefix rightPrefix →
        CommonRestorationApexList source cospan declaration depth
          leftSuffix rightSuffix →
        CommonRestorationApexList source cospan declaration depth
          (leftPrefix ++ leftSuffix) (rightPrefix ++ rightSuffix)
  | [], [], _, _, .nil _, suffix => suffix
  | _ :: _, _ :: _, _, _, .cons head tail, suffix =>
      .cons head (appendList cospan declaration tail suffix)

/-! ## Paired one-hole contexts

Static plans on two canonically aligned endpoints need not retain literally
the same one-hole context.  Their fixed siblings may have distinct semantic
atom spellings, and the selected occurrence may sit below binders or a quote
reset.  `Context` records the structural correspondence of the two contexts
while retaining common-restoration evidence for every fixed sibling.  Its two
depth indices make the root-to-hole depth transport explicit.
-/

/-- A pair of one-hole contexts whose fixed pieces meet at the same semantic
restoration apex.

The first depth is visible at the roots and the second at the holes.  Matching
constructors are part of the data, so this relation cannot identify distinct
operational shells. -/
inductive Context
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Nat → OneHoleContext → OneHoleContext → Prop where
  | hole (depth : Nat) :
      Context (source := source) cospan declaration depth depth .hole .hole
  | apply {depth holeDepth : Nat} (constructor : String)
      {leftBefore rightBefore leftAfter rightAfter : List Pattern}
      {leftInner rightInner : OneHoleContext}
      (before : CommonRestorationApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        leftBefore rightBefore)
      (inner : Context (source := source) cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        holeDepth leftInner rightInner)
      (after : CommonRestorationApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        leftAfter rightAfter) :
      Context (source := source) cospan declaration depth holeDepth
        (.apply constructor leftBefore leftInner leftAfter)
        (.apply constructor rightBefore rightInner rightAfter)
  | lambda {depth holeDepth : Nat} (binder : Option String)
      {leftInner rightInner : OneHoleContext}
      (inner : Context (source := source) cospan declaration
        (depth + 1) holeDepth
        leftInner rightInner) :
      Context (source := source) cospan declaration depth holeDepth
        (.lambda binder leftInner) (.lambda binder rightInner)
  | multiLambda {depth holeDepth arity : Nat} (binders : List String)
      {leftInner rightInner : OneHoleContext}
      (inner : Context (source := source) cospan declaration
        (depth + arity) holeDepth
        leftInner rightInner) :
      Context (source := source) cospan declaration depth holeDepth
        (.multiLambda arity binders leftInner)
        (.multiLambda arity binders rightInner)
  | substBody {depth holeDepth : Nat}
      {leftInner rightInner : OneHoleContext}
      {leftReplacement rightReplacement : Pattern}
      (inner : Context (source := source) cospan declaration
        (depth + 1) holeDepth
        leftInner rightInner)
      (replacement : CommonRestorationApex source cospan declaration depth
        leftReplacement rightReplacement) :
      Context (source := source) cospan declaration depth holeDepth
        (.substBody leftInner leftReplacement)
        (.substBody rightInner rightReplacement)
  | substReplacement {depth holeDepth : Nat}
      {leftBody rightBody : Pattern}
      {leftInner rightInner : OneHoleContext}
      (body : CommonRestorationApex source cospan declaration (depth + 1)
        leftBody rightBody)
      (inner : Context (source := source) cospan declaration depth holeDepth
        leftInner rightInner) :
      Context (source := source) cospan declaration depth holeDepth
        (.substReplacement leftBody leftInner)
        (.substReplacement rightBody rightInner)
  | collection {depth holeDepth : Nat} (collectionType : CollType)
      (rest : Option String)
      {leftBefore rightBefore leftAfter rightAfter : List Pattern}
      {leftInner rightInner : OneHoleContext}
      (before : CommonRestorationApexList source cospan declaration depth
        leftBefore rightBefore)
      (inner : Context (source := source) cospan declaration depth holeDepth
        leftInner rightInner)
      (after : CommonRestorationApexList source cospan declaration depth
        leftAfter rightAfter) :
      Context (source := source) cospan declaration depth holeDepth
        (.collection collectionType leftBefore leftInner leftAfter rest)
        (.collection collectionType rightBefore rightInner rightAfter rest)

namespace Context

/-- A context is aligned with itself at exactly its computed hole depth. -/
def refl
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    ∀ (depth : Nat) (context : OneHoleContext),
      CommonRestorationApex.Context (source := source) cospan declaration depth
        (restorationDepthThroughContext source depth context) context context
  | depth, .hole => .hole depth
  | depth, .apply constructor before inner after =>
      let childDepth :=
        if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth
      .apply constructor
        (CommonRestorationApex.reflList cospan declaration childDepth before)
        (refl cospan declaration childDepth inner)
        (CommonRestorationApex.reflList cospan declaration childDepth after)
  | depth, .lambda binder inner =>
      .lambda binder (refl cospan declaration (depth + 1) inner)
  | depth, .multiLambda arity binders inner =>
      .multiLambda binders
        (refl cospan declaration (depth + arity) inner)
  | depth, .substBody inner replacement =>
      .substBody (refl cospan declaration (depth + 1) inner)
        (CommonRestorationApex.refl cospan declaration depth replacement)
  | depth, .substReplacement body inner =>
      .substReplacement
        (CommonRestorationApex.refl cospan declaration (depth + 1) body)
        (refl cospan declaration depth inner)
  | depth, .collection collectionType before inner after rest =>
      .collection collectionType rest
        (CommonRestorationApex.reflList cospan declaration depth before)
        (refl cospan declaration depth inner)
        (CommonRestorationApex.reflList cospan declaration depth after)

/-- Fill two aligned contexts with one apex at their common hole depth. -/
def fill
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} :
    ∀ {depth holeDepth : Nat} {leftContext rightContext : OneHoleContext},
      CommonRestorationApex.Context (source := source) cospan declaration
        depth holeDepth leftContext rightContext →
      ∀ {left right : Pattern},
        CommonRestorationApex source cospan declaration holeDepth left right →
        CommonRestorationApex source cospan declaration depth
          (leftContext.fill left) (rightContext.fill right)
  | _, _, _, _, .hole _, _, _, apex => apex
  | _, _, _, _, .apply constructor before inner after, _, _, apex =>
      .apply constructor
        (CommonRestorationApex.appendList cospan declaration before
          (.cons (fill inner apex) after))
  | _, _, _, _, .lambda binder inner, _, _, apex =>
      .lambda binder (fill inner apex)
  | _, _, _, _, .multiLambda binders inner, _, _, apex =>
      .multiLambda binders (fill inner apex)
  | _, _, _, _, .substBody inner replacement, _, _, apex =>
      .subst (fill inner apex) replacement
  | _, _, _, _, .substReplacement body inner, _, _, apex =>
      .subst body (fill inner apex)
  | _, _, _, _, .collection collectionType rest before inner after, _, _,
      apex =>
      .collection collectionType rest
        (CommonRestorationApex.appendList cospan declaration before
          (.cons (fill inner apex) after))

/-- Negative canary: paired contexts cannot change an application shell into
a lambda shell. -/
theorem not_apply_lambda
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    {depth holeDepth : Nat} {constructor : String}
    {before after : List Pattern} {leftInner rightInner : OneHoleContext}
    {binder : Option String} :
    ¬ CommonRestorationApex.Context (source := source) cospan declaration
      depth holeDepth
      (.apply constructor before leftInner after) (.lambda binder rightInner) := by
  intro aligned
  cases aligned

end Context

/-- Lift a common-restoration apex through the same one-hole context on both
endpoints.

The hole evidence is required at the context-computed depth.  The result is
therefore valid through arbitrary ordinary binders, reflective quote resets,
substitution positions, and collection/application spines without adding a
new semantic equality premise. -/
noncomputable def throughContext
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    ∀ (context : OneHoleContext) (depth : Nat) {left right : Pattern},
      CommonRestorationApex source cospan declaration
          (restorationDepthThroughContext source depth context) left right →
        CommonRestorationApex source cospan declaration depth
          (context.fill left) (context.fill right)
  | .hole, _, _, _, apex => apex
  | .apply constructor before inner after, depth, left, right, apex => by
      let childDepth :=
        if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth
      let middle := throughContext cospan declaration inner childDepth apex
      let arguments := appendList cospan declaration
        (reflList cospan declaration childDepth before)
        (.cons middle (reflList cospan declaration childDepth after))
      exact .apply constructor arguments
  | .lambda binder inner, depth, left, right, apex =>
      .lambda binder
        (throughContext cospan declaration inner (depth + 1) apex)
  | .multiLambda arity binders inner, depth, left, right, apex =>
      .multiLambda binders
        (throughContext cospan declaration inner (depth + arity) apex)
  | .substBody inner replacement, depth, left, right, apex =>
      .subst
        (throughContext cospan declaration inner (depth + 1) apex)
        (refl cospan declaration depth replacement)
  | .substReplacement body inner, depth, left, right, apex =>
      .subst
        (refl cospan declaration (depth + 1) body)
        (throughContext cospan declaration inner depth apex)
  | .collection collectionType before inner after rest, depth, left, right,
      apex => by
      let middle := throughContext cospan declaration inner depth apex
      let elements := appendList cospan declaration
        (reflList cospan declaration depth before)
        (.cons middle (reflList cospan declaration depth after))
      exact .collection collectionType rest elements

private def commonRestorationApexList_toForall₂
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right : List Pattern}
    (alignment : CommonRestorationApexList source cospan declaration depth
      left right) :
    List.Forall₂
      (CommonRestorationApex source cospan declaration depth) left right :=
  match alignment with
  | .nil _ => .nil
  | .cons head tail =>
      .cons head (commonRestorationApexList_toForall₂ tail)

private def commonRestorationApexList_ofForall₂
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right : List Pattern}
    (alignment : List.Forall₂
      (CommonRestorationApex source cospan declaration depth) left right) :
    CommonRestorationApexList source cospan declaration depth left right :=
  match alignment with
  | .nil => .nil depth
  | .cons head tail =>
      .cons head (commonRestorationApexList_ofForall₂ tail)

mutual
  /-- Reverse a common restoration apex.  The parallel terminal reverses its
  finite permutation; every other constructor reverses recursively. -/
  noncomputable def symm
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : Pattern}
      (apex : CommonRestorationApex source cospan declaration depth left right) :
      CommonRestorationApex source cospan declaration depth right left :=
    match apex with
    | .leafAligned aligned =>
        .leafAligned (.leaf (fun currentDepth =>
          (ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
            aligned currentDepth).symm))
    | .apply constructor arguments =>
        .apply constructor (symmList arguments)
    | .lambda binder body => .lambda binder (symm body)
    | .multiLambda binders body => .multiLambda binders (symm body)
    | .subst body replacement => .subst (symm body) (symm replacement)
    | .collection collectionType rest elements =>
        .collection collectionType rest (symmList elements)
    | .parallel aligned permutation => by
        let reversed := symmList aligned
        let evidence := List.perm_comp_forall₂ permutation.symm
          (commonRestorationApexList_toForall₂ reversed)
        let reverseMiddle := Classical.choose evidence
        have reverseSpec := Classical.choose_spec evidence
        exact .parallel
          (commonRestorationApexList_ofForall₂ reverseSpec.1)
          reverseSpec.2

  /-- Listwise companion of `CommonRestorationApex.symm`. -/
  noncomputable def symmList
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : List Pattern}
      (apex : CommonRestorationApexList source cospan declaration depth
        left right) :
      CommonRestorationApexList source cospan declaration depth right left :=
    match apex with
    | .nil depth => .nil depth
    | .cons head tail => .cons (symm head) (symmList tail)
end

/-- A permutation of restoration-related entries, with positional alignment
and finite reordering retained as separate proof-relevant data.  This is the
list currency for canonical parallel inversion, which yields a multiset
correspondence rather than a positional zip. -/
structure Permutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (left right : List Pattern) : Type where
  middle : List Pattern
  aligned : CommonRestorationApexList source cospan declaration depth
    left middle
  permutation : List.Perm middle right

/-- Reindex both finite endpoints of an aligned permutation.  The operation
keeps occurrence order and semantic alignment separate: the left permutation
is transported through the pointwise relation, while the right permutation
is composed only after that alignment has been retained. -/
noncomputable def Permutation.of_endpoint_perms
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} {depth : Nat}
    {left left' right right' : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      left right)
    (leftPermutation : List.Perm left' left)
    (rightPermutation : List.Perm right' right) :
    Permutation (source := source) cospan declaration depth left' right' := by
  let evidence := List.perm_comp_forall₂ leftPermutation
    (commonRestorationApexList_toForall₂ alignment.aligned)
  let middle' := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  exact
    { middle := middle'
      aligned := commonRestorationApexList_ofForall₂ middleSpec.1
      permutation := middleSpec.2.trans
        (alignment.permutation.trans rightPermutation.symm) }

/- Eliminate a recursive apex into exact equality after common restoration.

The leaf case consumes `PatternLeafAligned`; the parallel case consumes the
permutation terminal; all remaining cases are genuine structural congruence.
-/
mutual
  def restored_eq
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : Pattern}
      (apex : CommonRestorationApex source cospan declaration depth left right) :
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth left =
        ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth right :=
    match apex with
    | .leafAligned aligned =>
        ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
          aligned depth
    | .apply constructor arguments => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.apply constructor) (restoredList_eq arguments)
    | .lambda binder body => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.lambda binder) (restored_eq body)
    | .multiLambda binders body => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.multiLambda _ binders) (restored_eq body)
    | .subst body replacement => by
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.subst.injEq]
        exact ⟨restored_eq body, restored_eq replacement⟩
    | .collection collectionType rest elements => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (fun patterns =>
          Pattern.collection collectionType patterns rest)
            (restoredList_eq elements)
    | .parallel aligned permutation => by
        let restore := ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth
        have restoredAlignment := restoredList_eq aligned
        have restoredPermutation : List.Perm
            (_root_.List.map restore _) (_root_.List.map restore _) :=
          (List.Perm.of_eq restoredAlignment).trans (permutation.map restore)
        exact cospan.substituteAt_canonicalizeByAt_parallel_eq_of_perm source
          depth declaration restoredPermutation

  /-- Listwise elimination for rigid congruence constructors. -/
  def restoredList_eq
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : List Pattern}
      (apex : CommonRestorationApexList source cospan declaration depth
        left right) :
      left.map (ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth) =
        right.map (ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth) :=
    match apex with
    | .nil depth => rfl
    | .cons head tail =>
        congrArg₂ List.cons (restored_eq head) (restoredList_eq tail)
end

/-- A family of restoration apexes indexed by every ambient depth is exactly
the uniform equality required at a semantic leaf.  This bridge keeps the two
quantifiers distinct: one apex witnesses one depth, while `RestoresTogether`
requires the entire depth-indexed family. -/
theorem restoresTogether_of_forall_apex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (apex : ∀ depth,
      CommonRestorationApex source cospan declaration depth left right) :
    ReflectiveContextSupport.RestoresTogether
      source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment left right := by
  intro depth
  exact restored_eq (apex depth)

/-- Uniform recursive apex evidence may be compressed to one semantic leaf
at any requested outer depth.  The premise deliberately remains
depth-indexed; equality at one selected depth is insufficient. -/
theorem leafAligned_of_forall_apex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (apex : ∀ depth,
      CommonRestorationApex source cospan declaration depth left right)
    (depth : Nat) :
    CommonRestorationApex source cospan declaration depth left right :=
  .leafAligned (.leaf (restoresTogether_of_forall_apex apex))

/-- Forget a proof-relevant aligned permutation to the permutation of its
restored compact meanings. -/
theorem Permutation.restored_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} {depth : Nat}
    {left right : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      left right) :
    List.Perm
      (left.map (ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        depth))
      (right.map (ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        depth)) := by
  rw [restoredList_eq alignment.aligned]
  exact alignment.permutation.map _

/-- Build the parallel apex from an occurrence-preserving alignment of the
post-canonicalization, post-splice frontiers. -/
theorem parallel_of_permutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {leftElements rightElements : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth leftElements))
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth rightElements))) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection leftElements none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection rightElements none)) :=
  .parallel alignment.aligned alignment.permutation

/-- A permutation of ordinary canonical images can be pulled back to an
occurrence-preserving permutation of the original right list, aligned
pointwise by canonical equality.  No injectivity of canonicalization is used:
duplicate and collapsing classes retain separate list occurrences. -/
theorem exists_forall₂_canonical_eq_of_map_perm
    (declaration : ReflectivePresentationDecl)
    {left right : List Pattern}
    (permutation : List.Perm
      (left.map (canonicalize declaration))
      (right.map (canonicalize declaration))) :
    ∃ middle,
      List.Forall₂
          (fun leftPattern rightPattern =>
            canonicalize declaration leftPattern =
              canonicalize declaration rightPattern)
          left middle ∧
        List.Perm middle right := by
  have rightGraph : List.Forall₂
      (fun canonicalPattern pattern =>
        canonicalPattern = canonicalize declaration pattern)
      (right.map (canonicalize declaration)) right := by
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr (fun _ _ => rfl)
  obtain ⟨middle, aligned, reordered⟩ :=
    List.perm_comp_forall₂ permutation rightGraph
  refine ⟨middle, ?_, reordered⟩
  simpa only [List.forall₂_map_left_iff] using aligned

/-- Lift a permutation of ordinary canonical classes through a local
common-apex constructor.  The callback receives membership in both original
endpoint lists, so typing, support, size descent, provenance, and occurrence
evidence can be recovered before recursive closure.  Multiplicities and
discarded positional identities are retained by the intermediate list. -/
noncomputable def Permutation.of_canonical_map_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : List Pattern}
    (permutation : List.Perm
      (left.map (canonicalize declaration))
      (right.map (canonicalize declaration)))
    (close : ∀ {leftPattern rightPattern},
      leftPattern ∈ left → rightPattern ∈ right →
      canonicalize declaration leftPattern =
          canonicalize declaration rightPattern →
        CommonRestorationApex source cospan declaration depth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration depth leftPattern)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration depth rightPattern)) :
    Permutation (source := source) cospan declaration depth
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth left)
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth right) := by
  let evidence :=
    exists_forall₂_canonical_eq_of_map_perm declaration permutation
  let middle := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  have aligned := middleSpec.1
  have reordered := middleSpec.2
  let normalize := canonicalizeByAt
    (cospan.commonSemanticPatternKeyAt source) declaration depth
  have liftAligned : ∀ {leftPatterns rightPatterns : List Pattern},
      List.Forall₂
          (fun leftPattern rightPattern =>
            canonicalize declaration leftPattern =
              canonicalize declaration rightPattern)
          leftPatterns rightPatterns →
        (∀ pattern ∈ leftPatterns, pattern ∈ left) →
        (∀ pattern ∈ rightPatterns, pattern ∈ right) →
        CommonRestorationApexList source cospan declaration depth
          (leftPatterns.map normalize) (rightPatterns.map normalize) := by
    intro leftPatterns rightPatterns relation leftMembership rightMembership
    induction relation with
    | nil => exact .nil depth
    | cons related _ inductionHypothesis =>
        exact .cons
          (close (leftMembership _ (by simp))
            (rightMembership _ (by simp)) related)
          (inductionHypothesis
            (fun pattern membership =>
              leftMembership pattern (by simp [membership]))
            (fun pattern membership =>
              rightMembership pattern (by simp [membership])))
  have normalizedAligned : CommonRestorationApexList source cospan declaration
      depth (left.map normalize) (middle.map normalize) :=
    liftAligned aligned (fun _ membership => membership)
      (fun pattern membership => reordered.mem_iff.mp membership)
  refine
    { middle := middle.map normalize
      aligned := ?_
      permutation := ?_ }
  simpa [normalize, canonicalizeListByAt_eq_map] using normalizedAligned
  simpa [normalize, canonicalizeListByAt_eq_map] using reordered.map normalize

/-- Away from the two root-changing reflective forms, ordinary canonical
root inversion lifts directly to the common-restoration apex.  The recursive
callback is invoked only for proper children and at the depth selected by the
rigid constructor: binders advance it, whereas this aligned arm cannot have a
quote head. -/
theorem of_canonicalRootAligned
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (close : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChild rightChild : Pattern},
      canonicalize declaration leftChild = canonicalize declaration rightChild →
        CommonRestorationApex source cospan declaration childRootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration leftChildDepth leftChild)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration rightChildDepth rightChild))
    {leftDepth rightDepth rootDepth : Nat} {left right : Pattern}
    (ordinaryHead : ∀ {constructor : String}
      {leftArguments rightArguments : List Pattern},
      left = .apply constructor leftArguments →
      right = .apply constructor rightArguments →
      constructor ≠ declaration.quoteConstructor →
      ReflectiveContextSupport.isQuoteConstructor source.costWholeReflectionProfile
        constructor = false)
    (aligned : CanonicalRootAligned declaration left right) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right) := by
  let key := cospan.commonSemanticPatternKeyAt source
  have closeList : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChildren rightChildren : List Pattern},
      List.Forall₂
          (fun leftChild rightChild =>
            canonicalize declaration leftChild =
              canonicalize declaration rightChild)
          leftChildren rightChildren →
        CommonRestorationApexList source cospan declaration childRootDepth
          (canonicalizeListByAt key declaration leftChildDepth leftChildren)
          (canonicalizeListByAt key declaration rightChildDepth rightChildren) := by
    intro leftChildDepth rightChildDepth childRootDepth leftChildren
      rightChildren children
    rw [canonicalizeListByAt_eq_map, canonicalizeListByAt_eq_map]
    induction children with
    | nil => exact .nil childRootDepth
    | cons related _ inductionHypothesis =>
        exact .cons
          (close leftChildDepth rightChildDepth childRootDepth related)
          inductionHypothesis
  cases aligned with
  | bvar index => exact of_eq cospan declaration rootDepth rfl
  | fvar name => exact of_eq cospan declaration rootDepth rfl
  | @apply constructor ne leftArguments rightArguments children =>
      have quoteStatus := ordinaryHead rfl rfl ne
      have arguments : CommonRestorationApexList source cospan declaration
          (if ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile constructor then 0 else rootDepth)
          (canonicalizeListByAt key declaration leftDepth leftArguments)
          (canonicalizeListByAt key declaration rightDepth rightArguments) := by
        simpa [quoteStatus] using
          closeList leftDepth rightDepth rootDepth children
      simpa [canonicalizeByAt, ne] using
        (CommonRestorationApex.apply constructor arguments)
  | lambda binder body =>
      exact .lambda binder
        (close (leftDepth + 1) (rightDepth + 1) (rootDepth + 1) body)
  | multiLambda arity binders body =>
      exact .multiLambda binders
        (close (leftDepth + arity) (rightDepth + arity)
          (rootDepth + arity) body)
  | subst body replacement =>
      exact .subst
        (close (leftDepth + 1) (rightDepth + 1) (rootDepth + 1) body)
        (close leftDepth rightDepth rootDepth replacement)
  | @collection collectionType ne leftElements rightElements children =>
      have notParallel :
          (collectionType == declaration.parallelCollection) = false :=
        beq_eq_false_iff_ne.mpr ne
      simpa [canonicalizeByAt, notParallel] using
        (CommonRestorationApex.collection collectionType none
          (closeList leftDepth rightDepth rootDepth children))
  | collectionRest collectionType rest children =>
      exact .collection collectionType (some rest)
        (closeList leftDepth rightDepth rootDepth children)

/-- A left Quote/Drop shell contributes no additional restoration evidence:
keyed canonicalization removes it and resets only the payload's quote-visible
depth.  The recursive apex may therefore compare that depth-zero payload with
an endpoint canonicalized at a different visible depth. -/
theorem of_quoteDrop_left
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {leftDepth rightDepth rootDepth : Nat} {inner right : Pattern}
    (innerApex : CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration 0 inner)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right)) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [inner]]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right) := by
  simpa only [canonicalizeByAt_quote_drop _ declaration quote_ne_drop] using
    innerApex

/-- Right-oriented companion of `of_quoteDrop_left`. -/
theorem of_quoteDrop_right
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {leftDepth rightDepth rootDepth : Nat} {left inner : Pattern}
    (innerApex : CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration 0 inner)) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [inner]])) := by
  simpa only [canonicalizeByAt_quote_drop _ declaration quote_ne_drop] using
    innerApex

/-- Equality transports only the indices of a common apex; it adds no
semantic evidence. -/
theorem reindex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right left' right' : Pattern}
    (leftEq : left = left') (rightEq : right = right')
    (apex : CommonRestorationApex source cospan declaration depth left right) :
    CommonRestorationApex source cospan declaration depth left' right' := by
  cases leftEq
  cases rightEq
  exact apex

/-- Positive rigid-leaf canary. -/
theorem bvar_refl
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth index : Nat) :
    CommonRestorationApex source cospan declaration depth
      (.bvar index) (.bvar index) :=
  .leafAligned (.bvar index)

/-- Positive non-reflexive-permutation canary.  Two rigid bound leaves may
occur in opposite parallel orders; the apex records the swap rather than
pretending it is positional alignment. -/
theorem parallel_swap_bvars
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth first second : Nat) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar first, .bvar second] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar second, .bvar first] none)) := by
  apply CommonRestorationApex.parallel
  · exact reflList cospan declaration depth _
  · simpa [canonicalizeListByAt, canonicalizeByAt, parallelContents,
      parallelSplice] using
      (List.Perm.swap (Pattern.bvar second) (Pattern.bvar first) [])

/-- A nested parallel permutation reaches the same spliced frontier on both
sides.  This is the regression for the central construction theorem: the
parallel constructor is indexed by `parallelContents` after recursive keyed
canonicalization, rather than by the raw element lists. -/
theorem parallel_nested_reassociation_bvars
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar 0,
            .collection declaration.parallelCollection
              [.bvar 1, .bvar 2] none] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar 2,
            .collection declaration.parallelCollection
              [.bvar 0, .bvar 1] none] none)) := by
  let key := cospan.commonSemanticPatternKeyAt source depth
  have lengthTwelve :
      (normalizeParallelElementsBy key declaration
        [.bvar 1, .bvar 2]).length = 2 := by
    have permutation :=
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
      [.bvar 1, .bvar 2]
    simpa [normalizeParallelElementsBy, parallelSplice] using
      permutation.length_eq
  have lengthZeroOne :
      (normalizeParallelElementsBy key declaration
        [.bvar 0, .bvar 1]).length = 2 := by
    have permutation :=
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
      [.bvar 0, .bvar 1]
    simpa [normalizeParallelElementsBy, parallelSplice] using
      permutation.length_eq
  apply CommonRestorationApex.parallel
  · exact reflList cospan declaration depth _
  · simp only [canonicalizeListByAt, canonicalizeByAt]
    rw [show collapseParallel declaration
        (normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2]) =
          .collection declaration.parallelCollection
            (normalizeParallelElementsBy key declaration
              [.bvar 1, .bvar 2]) none by
          exact collapseParallel_eq_collection_of_length_ge_two declaration
            (by omega),
      show collapseParallel declaration
        (normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1]) =
          .collection declaration.parallelCollection
            (normalizeParallelElementsBy key declaration
              [.bvar 0, .bvar 1]) none by
          exact collapseParallel_eq_collection_of_length_ge_two declaration
            (by omega)]
    simp [parallelContents, parallelSplice, key]
    have twelvePermutation : List.Perm
        (normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2])
        [.bvar 1, .bvar 2] := by
      simpa [normalizeParallelElementsBy, parallelSplice] using
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
          [.bvar 1, .bvar 2])
    have zeroOnePermutation : List.Perm
        (normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1])
        [.bvar 0, .bvar 1] := by
      simpa [normalizeParallelElementsBy, parallelSplice] using
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
          [.bvar 0, .bvar 1])
    have twelveNoUnit :
        (normalizeParallelElementsBy key declaration
          [.bvar 1, .bvar 2]).filter
            (fun pattern => !decide
              (pattern = .apply declaration.parallelUnitConstructor [])) =
          normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2] := by
      apply List.filter_eq_self.mpr
      intro pattern membership
      have rawMembership := twelvePermutation.mem_iff.mp membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMembership
      rcases rawMembership with rfl | rfl <;> simp
    have zeroOneNoUnit :
        (normalizeParallelElementsBy key declaration
          [.bvar 0, .bvar 1]).filter
            (fun pattern => !decide
              (pattern = .apply declaration.parallelUnitConstructor [])) =
          normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1] := by
      apply List.filter_eq_self.mpr
      intro pattern membership
      have rawMembership := zeroOnePermutation.mem_iff.mp membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMembership
      rcases rawMembership with rfl | rfl <;> simp
    rw [twelveNoUnit, zeroOneNoUnit]
    have leftPermutation := List.Perm.cons (Pattern.bvar 0) twelvePermutation
    have rightToRotated := List.Perm.cons (Pattern.bvar 2) zeroOnePermutation
    have rotatedToCommon : List.Perm
        [Pattern.bvar 2, Pattern.bvar 0, Pattern.bvar 1]
        [Pattern.bvar 0, Pattern.bvar 1, Pattern.bvar 2] :=
      (List.Perm.swap (Pattern.bvar 0) (Pattern.bvar 2)
        [Pattern.bvar 1]).trans
        (List.Perm.cons (Pattern.bvar 0)
          (List.Perm.swap (Pattern.bvar 1) (Pattern.bvar 2) []))
    exact leftPermutation.trans (rightToRotated.trans rotatedToCommon).symm

/-- Positional leaf alignment cannot express even the flat rigid swap that
the restoration apex admits.  The semantic leaf escape hatch does not help:
restoration leaves bound variables unchanged, so the two lists remain
different. -/
theorem parallel_swap_bvars_not_patternLeafAligned
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (first second : Nat) (different : first ≠ second) :
    ¬ PatternLeafAligned
      (ReflectiveContextSupport.RestoresTogether
        source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment)
      (.collection .hashBag [.bvar first, .bvar second] none)
      (.collection .hashBag [.bvar second, .bvar first] none) := by
  intro aligned
  have atZero :=
    ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
      aligned 0
  simp only [ReflectiveContextSupport.substituteAt,
    List.map_cons, List.map_nil, Pattern.collection.injEq,
    true_and] at atZero
  exact different (Pattern.bvar.inj (List.cons.inj atZero.1).1)

/-- Restoring a keyed canonical frame does not generically commute with the
ordinary canonicalizer unless the assigned opaque values are themselves
canonical for that declaration.  Here the keyed canonicalizer correctly
leaves one atom opaque, restoration reveals a noncanonical Quote/Drop value,
and ordinary canonicalization subsequently contracts it.

This counterexample rules out a tempting shortcut in the static common-apex
proof: recursive canonicality of boundary values must be established before
any fixed-point argument can replace occurrence-aware restoration. -/
theorem substituteAt_canonicalizeByAt_not_commute_without_canonical_assignment
    (source : CIGSLT) (declaration : ReflectivePresentationDecl)
    (different : declaration.dropConstructor ≠
      declaration.quoteConstructor) :
    let support : ContextSupport.Support := fun _ => []
    let assignment : ContextSupport.Assignment :=
      fun _ => Pattern.apply declaration.quoteConstructor
        [Pattern.apply declaration.dropConstructor [Pattern.fvar "payload"]]
    let key : Nat → Pattern → Nat := fun _ pattern =>
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          support assignment 0 pattern)
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile support
        assignment 0
        (canonicalizeByAt key declaration 0 (.fvar "atom")) ≠
      canonicalize declaration
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile support
          assignment 0 (.fvar "atom")) := by
  dsimp only
  simp only [canonicalizeByAt, ReflectiveContextSupport.substituteAt,
    List.length_nil, Nat.sub_zero,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  rw [canonicalize_quote_drop declaration different]
  exact Pattern.noConfusion

/-- Negative rigid-leaf canary: the apex cannot identify distinct bound
indices because neither restoration nor permutation changes a bound leaf. -/
theorem bvar_ne_not
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth leftIndex rightIndex : Nat)
    (different : leftIndex ≠ rightIndex) :
    ¬ CommonRestorationApex source cospan declaration depth
      (.bvar leftIndex) (.bvar rightIndex) := by
  intro apex
  have restored := apex.restored_eq
  have restored' : Pattern.bvar leftIndex = Pattern.bvar rightIndex := by
    simpa only [ReflectiveContextSupport.substituteAt] using restored
  exact different (Pattern.bvar.inj restored')

end CommonRestorationApex

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
