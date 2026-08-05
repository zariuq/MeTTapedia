import Mettapedia.GSLT.LanguageDef.CostElaborationDecoration
import Mettapedia.GSLT.LanguageDef.EquationOccurrence

/-!
# Fiber transport for proof-relevant Cost decorations

Authored equations may duplicate or discard a boundary occurrence. A valid
decoration transport therefore needs a finite occurrence map, not an equality
of boundary lists and not a first-match lookup. This module isolates that
nonlinear bookkeeping before the semantic lifted-generator relation is built.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace EquationSemantics.AuthoredEquationInstanceWitness

/-- Map one exact authored equation occurrence into either generated static
Cost copy.  The selected source declaration, orientation, and bindings remain
computational data; this is stronger than merely proving that some generated
equation instance exists between the mapped endpoints. -/
def mapCostStatic (source : CIGSLT) (color : CostStaticColor)
    {input output : Pattern}
    (witness : AuthoredEquationInstanceWitness defaultBasePremises
      source.theory.presentation.presentation.language input output) :
    AuthoredEquationInstanceWitness defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) input)
      (mapPattern (color.symbols source) output) := by
  cases witness with
  | @forward fuel equation initialBindings finalBindings matched premises
      target_eq =>
      have retypable := source.equationsRetypable equation.1 equation.2
      have final_eq : finalBindings = initialBindings := by
        have emptyPremises :
            PremisesAt defaultBasePremises
              source.theory.presentation.presentation.language fuel
              initialBindings [] finalBindings := by
          simpa [retypable.premiseFree] using premises
        cases emptyPremises
        rfl
      subst finalBindings
      have sourceMatch :=
        Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound matched
      have mappedMatch := matchRel_mapCostStatic source color sourceMatch
      have mappedMatched :=
        Mettapedia.OSLF.MeTTaIL.MatchSpec.matchRel_complete mappedMatch
      have leftCovered := matchRel_coversPattern sourceMatch
      have rightCovered :
          BindingsCoverPattern initialBindings equation.1.right := by
        intro name rightMembership
        apply leftCovered name
        simpa [LanguageDef.patternFvarNames_nil] using
          rightFvar_mem_left_of_validatedEquation_noPremises
            source.theory.presentation.presentation.language
            source.theory.presentation.presentation.valid equation.1
            equation.2 retypable.premiseFree name
            (by simpa [LanguageDef.patternFvarNames_nil] using rightMembership)
      refine .forward fuel
        ⟨costStaticEquationDecl source color equation.1,
          costStaticEquationDecl_mem source color equation.1 equation.2⟩
        (mapCostStaticBindings source color initialBindings)
        (mapCostStaticBindings source color initialBindings) ?_ ?_ ?_
      · simpa only [costStaticEquationDecl_left] using mappedMatched
      · rw [costStaticEquationDecl_premises _ _ _ retypable.premiseFree]
        exact .nil _
      · rw [costStaticEquationDecl_right]
        calc
          applyBindings
                (mapCostStaticBindings source color initialBindings)
                (mapCostStaticSchemaPattern source color equation.1.right) =
              mapPattern (color.symbols source)
                (applyBindings initialBindings equation.1.right) :=
            applyBindings_mapCostStatic source color initialBindings
              equation.1.right retypable.rightInstantiationStable rightCovered
          _ = mapPattern (color.symbols source) output :=
            congrArg (mapPattern (color.symbols source)) target_eq
  | @reverse fuel equation initialBindings finalBindings matched premises
      target_eq =>
      have retypable := source.equationsRetypable equation.1 equation.2
      have final_eq : finalBindings = initialBindings := by
        have emptyPremises :
            PremisesAt defaultBasePremises
              source.theory.presentation.presentation.language fuel
              initialBindings [] finalBindings := by
          simpa [retypable.premiseFree] using premises
        cases emptyPremises
        rfl
      subst finalBindings
      have sourceMatch :=
        Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound matched
      have mappedMatch := matchRel_mapCostStatic source color sourceMatch
      have mappedMatched :=
        Mettapedia.OSLF.MeTTaIL.MatchSpec.matchRel_complete mappedMatch
      have rightCovered := matchRel_coversPattern sourceMatch
      have leftCovered :
          BindingsCoverPattern initialBindings equation.1.left := by
        intro name leftMembership
        apply rightCovered name
        exact
          LanguageDef.equation_leftFvar_mem_right_of_executionFlowErrors_eq_nil
            source.theory.presentation.presentation.language
            source.theory.executionProfile.relationModes
            source.sourceExecutionFlowErrors_eq_nil equation.1 equation.2
            retypable.premiseFree name leftMembership
      refine .reverse fuel
        ⟨costStaticEquationDecl source color equation.1,
          costStaticEquationDecl_mem source color equation.1 equation.2⟩
        (mapCostStaticBindings source color initialBindings)
        (mapCostStaticBindings source color initialBindings) ?_ ?_ ?_
      · simpa only [costStaticEquationDecl_right] using mappedMatched
      · rw [costStaticEquationDecl_premises _ _ _ retypable.premiseFree]
        exact .nil _
      · rw [costStaticEquationDecl_left]
        calc
          applyBindings
                (mapCostStaticBindings source color initialBindings)
                (mapCostStaticSchemaPattern source color equation.1.left) =
              mapPattern (color.symbols source)
                (applyBindings initialBindings equation.1.left) :=
            applyBindings_mapCostStatic source color initialBindings
              equation.1.left retypable.leftInstantiationStable leftCovered
          _ = mapPattern (color.symbols source) output :=
            congrArg (mapPattern (color.symbols source)) target_eq

/-- Forgetting the proof-relevant mapped occurrence agrees with the existing
proposition-valued Cost embedding of the same source occurrence. -/
theorem erase_mapCostStatic (source : CIGSLT) (color : CostStaticColor)
    {input output : Pattern}
    (witness : AuthoredEquationInstanceWitness defaultBasePremises
      source.theory.presentation.presentation.language input output) :
    (witness.mapCostStatic source color).erase =
      equationInstance_mapCostStatic source color witness.erase :=
  Subsingleton.elim _ _

end EquationSemantics.AuthoredEquationInstanceWitness

namespace EquationSemantics.AuthoredGeneratorWitness

/-- Map one exact authored contextual generator occurrence into either static
Cost copy.  Equation and reflective identities are transported, rather than
forgotten and existentially reconstructed afterward. -/
def mapCostStatic (source : CIGSLT) (color : CostStaticColor)
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness defaultBasePremises
      source.theory.presentation.presentation.language left right) :
    AuthoredGeneratorWitness defaultBasePremises source.costWholeLanguage
      (mapPattern (color.symbols source) left)
      (mapPattern (color.symbols source) right) := by
  cases witness with
  | @equation context redex contractum instanceWitness =>
      rw [← CIGSLT.mapOneHoleContext_fill,
        ← CIGSLT.mapOneHoleContext_fill]
      exact .equation (CIGSLT.mapOneHoleContext (color.symbols source) context)
        (instanceWitness.mapCostStatic source color)
  | @reflective context declaration redex contractum representatives =>
      rw [← CIGSLT.mapOneHoleContext_fill,
        ← CIGSLT.mapOneHoleContext_fill]
      exact .reflective
        (CIGSLT.mapOneHoleContext (color.symbols source) context)
        ⟨costStaticReflectivePresentationDecl source color declaration.1,
          costStaticReflectivePresentationDecl_mem source color declaration.1
            declaration.2⟩
        (canonicalize_eq_mapCostStatic source color declaration.1 declaration.2
          representatives)

/-- Support erasure commutes with the proof-relevant Cost embedding. -/
theorem erase_mapCostStatic (source : CIGSLT) (color : CostStaticColor)
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness defaultBasePremises
      source.theory.presentation.presentation.language left right) :
    (witness.mapCostStatic source color).erase =
      equationContextStep_mapCostStatic source color witness.erase :=
  Subsingleton.elim _ _

/-- The exact mapped occurrence remains an authored equation path after any
certified ambient binder embedding.  Occurrence identity is retained by the
input witness; the proposition-valued conclusion is its semantic support
projection. -/
theorem mapCostStatic_renameAmbientBVarsAt
    (source : CIGSLT) (color : CostStaticColor)
    (stable : WellSorted.SupportedEquationAmbientRenamingStable
      source.costWholeLanguage)
    (rename : Nat → Nat) (strict : StrictMono rename) (depth : Nat)
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness defaultBasePremises
      source.theory.presentation.presentation.language left right) :
    EquationEquiv defaultBasePremises source.costWholeLanguage
      (ContextSubstitution.renameAmbientBVarsAt rename depth
        (mapPattern (color.symbols source) left))
      (ContextSubstitution.renameAmbientBVarsAt rename depth
        (mapPattern (color.symbols source) right)) :=
  WellSorted.equationContextStep_renameAmbientBVarsAt stable rename strict depth
    (witness.mapCostStatic source color).erase

/-- Specialize exact occurrence transport to the intrinsic binder thinning
used by Cost static regions. -/
theorem mapCostStatic_thickenAmbientBVars
    (source : CIGSLT) (color : CostStaticColor)
    (stable : WellSorted.SupportedEquationAmbientRenamingStable
      source.costWholeLanguage)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) {left right : Pattern}
    (witness : AuthoredGeneratorWitness defaultBasePremises
      source.theory.presentation.presentation.language left right) :
    EquationEquiv defaultBasePremises source.costWholeLanguage
      (thinning.thickenAmbientBVars depth
        (mapPattern (color.symbols source) left))
      (thinning.thickenAmbientBVars depth
        (mapPattern (color.symbols source) right)) := by
  simpa only [CostStaticBinderThinning.thickenAmbientBVars_eq_renameAmbientBVarsAt]
    using witness.mapCostStatic_renameAmbientBVarsAt source color stable
      thinning.toTargetIndex thinning.toTargetIndex_strictMono depth

/-- Supported substitution acts on the exact mapped occurrence whenever its
two endpoints are packaged in the same certified support fibre.  This is the
substitution half of the Cost action before ambient binder reinsertion. -/
theorem mapCostStatic_substitute
    (source : CIGSLT) (color : CostStaticColor)
    (stable : WellSorted.SupportedEquationSubstitutionStable
      source.costWholeLanguage)
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftEndpoint : WellSorted.SupportSafeOpenPattern
      source.costWholeLanguage sourceFree support bound type)
    (rightEndpoint : WellSorted.SupportSafeOpenPattern
      source.costWholeLanguage sourceFree support bound type)
    (left_eq : leftEndpoint.term.1 =
      mapPattern (color.symbols source) left)
    (right_eq : rightEndpoint.term.1 =
      mapPattern (color.symbols source) right)
    (assignment : WellSorted.SupportedOpenAssignment
      source.costWholeLanguage sourceFree targetFree support)
    (witness : AuthoredGeneratorWitness defaultBasePremises
      source.theory.presentation.presentation.language left right) :
    EquationEquiv defaultBasePremises source.costWholeLanguage
      (leftEndpoint.substitute assignment).1
      (rightEndpoint.substitute assignment).1 := by
  apply WellSorted.SupportSafeOpenPattern.equationGenerator_substitute stable
    assignment leftEndpoint rightEndpoint
  simpa [WellSorted.SupportSafeOpenPattern.equationGenerator, left_eq,
    right_eq] using (witness.mapCostStatic source color).erase

end EquationSemantics.AuthoredGeneratorWitness

namespace CostRegionBoundary

/-- Two boundaries inhabit the same source/target typing and reflective-
support fiber. Their compact contents may differ along an authored semantic
step and are therefore deliberately not part of this relation. -/
structure SameFiber (first second : CostRegionBoundary) : Prop where
  type_eq : first.type = second.type
  support_eq : first.support = second.support
  targetType_eq : first.targetType = second.targetType
  targetSupport_eq : first.targetSupport = second.targetSupport

@[refl]
theorem sameFiber_refl (boundary : CostRegionBoundary) :
    SameFiber boundary boundary :=
  ⟨rfl, rfl, rfl, rfl⟩

@[symm]
theorem SameFiber.symm {first second : CostRegionBoundary}
    (same : SameFiber first second) : SameFiber second first :=
  ⟨same.type_eq.symm, same.support_eq.symm, same.targetType_eq.symm,
    same.targetSupport_eq.symm⟩

@[trans]
theorem SameFiber.trans {first middle last : CostRegionBoundary}
    (firstMiddle : SameFiber first middle)
    (middleLast : SameFiber middle last) : SameFiber first last :=
  ⟨firstMiddle.type_eq.trans middleLast.type_eq,
    firstMiddle.support_eq.trans middleLast.support_eq,
    firstMiddle.targetType_eq.trans middleLast.targetType_eq,
    firstMiddle.targetSupport_eq.trans middleLast.targetSupport_eq⟩

end CostRegionBoundary

namespace CostStaticPlanDecoration

/-- Equality of the complete static typing/support fiber, without requiring
the compact pattern, abstract skeleton, boundary occurrences, or declaration
plan to remain syntactically fixed. -/
structure SameFiber {source : CIGSLT}
    (first second : CostStaticPlanDecoration source) : Prop where
  sourceBound_eq : first.sourceBound = second.sourceBound
  targetBound_eq : first.targetBound = second.targetBound
  sourceAvailable_eq : first.sourceAvailable = second.sourceAvailable
  outer_eq : first.outer = second.outer
  sourceType_eq : first.sourceType = second.sourceType

@[refl]
theorem sameFiber_refl {source : CIGSLT}
    (decoration : CostStaticPlanDecoration source) :
    SameFiber decoration decoration :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

@[symm]
theorem SameFiber.symm {source : CIGSLT}
    {first second : CostStaticPlanDecoration source}
    (same : SameFiber first second) : SameFiber second first :=
  ⟨same.sourceBound_eq.symm, same.targetBound_eq.symm,
    same.sourceAvailable_eq.symm, same.outer_eq.symm,
    same.sourceType_eq.symm⟩

@[trans]
theorem SameFiber.trans {source : CIGSLT}
    {first middle last : CostStaticPlanDecoration source}
    (firstMiddle : SameFiber first middle)
    (middleLast : SameFiber middle last) : SameFiber first last :=
  ⟨firstMiddle.sourceBound_eq.trans middleLast.sourceBound_eq,
    firstMiddle.targetBound_eq.trans middleLast.targetBound_eq,
    firstMiddle.sourceAvailable_eq.trans middleLast.sourceAvailable_eq,
    firstMiddle.outer_eq.trans middleLast.outer_eq,
    firstMiddle.sourceType_eq.trans middleLast.sourceType_eq⟩

end CostStaticPlanDecoration

namespace CostTreeDecoration

/-- Equality of the generated Cost typing and binder split carried by two
recursive decorations. Raw patterns and structural choices may be transported
but cannot silently cross this fiber. -/
structure SameFiber {source : CIGSLT}
    (first second : CostTreeDecoration source) : Prop where
  available_eq : first.available = second.available
  outer_eq : first.outer = second.outer
  type_eq : first.type = second.type

@[refl]
theorem sameFiber_refl {source : CIGSLT}
    (decoration : CostTreeDecoration source) :
    SameFiber decoration decoration :=
  ⟨rfl, rfl, rfl⟩

@[symm]
theorem SameFiber.symm {source : CIGSLT}
    {first second : CostTreeDecoration source}
    (same : SameFiber first second) : SameFiber second first :=
  ⟨same.available_eq.symm, same.outer_eq.symm, same.type_eq.symm⟩

@[trans]
theorem SameFiber.trans {source : CIGSLT}
    {first middle last : CostTreeDecoration source}
    (firstMiddle : SameFiber first middle)
    (middleLast : SameFiber middle last) : SameFiber first last :=
  ⟨firstMiddle.available_eq.trans middleLast.available_eq,
    firstMiddle.outer_eq.trans middleLast.outer_eq,
    firstMiddle.type_eq.trans middleLast.type_eq⟩

end CostTreeDecoration

/-- A finite contravariant occurrence map from target boundaries back to the
source occurrences that supply them.

The map may be non-injective (duplication) or non-surjective (discarding).
Every target occurrence must nevertheless come from a source occurrence in
the same exact type/support fiber, so a boundary cannot be manufactured. -/
structure CostBoundaryFiberMap (source : CIGSLT)
    (sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)) where
  pullback : Fin targetBoundaries.length → Fin sourceBoundaries.length
  preservesFiber : ∀ targetIndex,
    CostRegionBoundary.SameFiber
      (sourceBoundaries.get (pullback targetIndex)).1
      (targetBoundaries.get targetIndex).1

namespace CostBoundaryFiberMap

/-- Identity occurrence transport. -/
def identity {source : CIGSLT}
    (boundaries : List (CostRegionBoundary × CostTreeDecoration source)) :
    CostBoundaryFiberMap source boundaries boundaries where
  pullback := id
  preservesFiber := fun _index => CostRegionBoundary.sameFiber_refl _

/-- Compose nonlinear occurrence transports by composing their pullbacks. -/
def comp {source : CIGSLT}
    {first middle last :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (firstToMiddle : CostBoundaryFiberMap source first middle)
    (middleToLast : CostBoundaryFiberMap source middle last) :
    CostBoundaryFiberMap source first last where
  pullback := fun index =>
    firstToMiddle.pullback (middleToLast.pullback index)
  preservesFiber := fun index =>
    (firstToMiddle.preservesFiber
      (middleToLast.pullback index)).trans
        (middleToLast.preservesFiber index)

/-- A boundary occurrence map lifts a recursive decoration relation when
every target child is related to the source child selected by its pullback.
This is where duplicated targets deliberately share one source occurrence. -/
def Lifts {source : CIGSLT}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (transport : CostBoundaryFiberMap source sourceBoundaries targetBoundaries)
    (relation : CostTreeDecoration source → CostTreeDecoration source → Prop) :
    Prop :=
  ∀ targetIndex,
    relation
      (sourceBoundaries.get (transport.pullback targetIndex)).2
      (targetBoundaries.get targetIndex).2

/-- Identity occurrence transport lifts every reflexive decoration
relation. -/
theorem identity_lifts {source : CIGSLT}
    {relation : CostTreeDecoration source → CostTreeDecoration source → Prop}
    (reflexive : ∀ decoration, relation decoration decoration)
    (boundaries : List (CostRegionBoundary × CostTreeDecoration source)) :
    (identity boundaries).Lifts relation := by
  intro index
  exact reflexive _

/-- Lifted recursive decoration transport composes whenever the child
relation is transitive. -/
theorem comp_lifts {source : CIGSLT}
    {relation : CostTreeDecoration source → CostTreeDecoration source → Prop}
    (transitive : ∀ {first middle last},
      relation first middle → relation middle last → relation first last)
    {first middle last :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {firstToMiddle : CostBoundaryFiberMap source first middle}
    {middleToLast : CostBoundaryFiberMap source middle last}
    (firstLift : firstToMiddle.Lifts relation)
    (secondLift : middleToLast.Lifts relation) :
    (comp firstToMiddle middleToLast).Lifts relation := by
  intro index
  exact transitive
    (firstLift (middleToLast.pullback index))
    (secondLift index)

/-- A boundary transport is determined by its finite occurrence map; the
fiber law is proposition-valued. -/
@[ext]
theorem ext {source : CIGSLT}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {first second : CostBoundaryFiberMap source sourceBoundaries
      targetBoundaries}
    (pullback_eq : first.pullback = second.pullback) : first = second := by
  cases first
  cases second
  cases pullback_eq
  rfl

@[simp]
theorem identity_comp {source : CIGSLT}
    {first last : List (CostRegionBoundary × CostTreeDecoration source)}
    (transport : CostBoundaryFiberMap source first last) :
    comp (identity first) transport = transport := by
  apply ext
  funext index
  rfl

@[simp]
theorem comp_identity {source : CIGSLT}
    {first last : List (CostRegionBoundary × CostTreeDecoration source)}
    (transport : CostBoundaryFiberMap source first last) :
    comp transport (identity last) = transport := by
  apply ext
  funext index
  rfl

@[simp]
theorem comp_assoc {source : CIGSLT}
    {first second third fourth :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (firstSecond : CostBoundaryFiberMap source first second)
    (secondThird : CostBoundaryFiberMap source second third)
    (thirdFourth : CostBoundaryFiberMap source third fourth) :
    comp (comp firstSecond secondThird) thirdFourth =
      comp firstSecond (comp secondThird thirdFourth) := by
  apply ext
  funext index
  rfl

/-- Any boundary family can discard all occurrences. -/
def discardAll {source : CIGSLT}
    (sourceBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)) :
    CostBoundaryFiberMap source sourceBoundaries [] where
  pullback := Fin.elim0
  preservesFiber := fun index => Fin.elim0 index

/-- No transport can create a target occurrence from an empty source family. -/
theorem noCreationFromEmpty {source : CIGSLT}
    {targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (targetIndex : Fin targetBoundaries.length) :
    IsEmpty (CostBoundaryFiberMap source [] targetBoundaries) :=
  ⟨fun transport => Fin.elim0 (transport.pullback targetIndex)⟩

end CostBoundaryFiberMap

/-- One proof-relevant declaration choice retained inside a static plan.

Applications carry the exact intrinsic generated declaration.  Bare
collections carry the exact authored collection candidate, which compact
`Pattern` syntax does not record.  Boundary occurrences additionally retain
the declaration or opposite-colour collection choice that caused the cut. -/
inductive CostStaticChoiceOccurrence (source : CIGSLT) where
  | application (position : OneHoleContext) (sourceLabel : String)
      (arguments : List Pattern)
      (constructor : source.DeclaredCostConstructor)
  | collection (position : OneHoleContext) (collectionType : CollType)
      (elements : List Pattern) (rest : Option String)
      (choice : CostCollectionTypingChoice)
  | boundaryApplication (position : OneHoleContext)
      (constructor : source.DeclaredCostConstructor)
      (boundary : CostRegionBoundary)
  | boundaryCollection (position : OneHoleContext)
      (collectionType : CollType)
      (choice : CostCollectionTypingChoice)
      (boundary : CostRegionBoundary)

namespace CostStaticChoiceOccurrence

/-- Exact syntactic position retained by a declaration/collection occurrence.
It is used to distinguish the unchanged outer context of a generator from the
redex interior, where the authored rule may introduce or delete constructors. -/
def position {source : CIGSLT} :
    CostStaticChoiceOccurrence source → OneHoleContext
  | .application position _ _ _ => position
  | .collection position _ _ _ _ => position
  | .boundaryApplication position _ _ => position
  | .boundaryCollection position _ _ _ => position

/-- Exact source-skeleton node selected by one retained choice.  Arguments and
collection elements are observations of the current endpoint; `SameFiber`
below deliberately permits them to change along an authored equation. -/
def sitePattern {source : CIGSLT} :
    CostStaticChoiceOccurrence source → Pattern
  | .application _ sourceLabel arguments _ => .apply sourceLabel arguments
  | .collection _ collectionType elements rest _ =>
      .collection collectionType elements rest
  | .boundaryApplication _ _ boundary =>
      .fvar (costRegionBoundaryVariableName boundary)
  | .boundaryCollection _ _ _ boundary =>
      .fvar (costRegionBoundaryVariableName boundary)

/-- Two retained choices inhabit the same proof-relevant fibre.

Declaration and collection identity are exact.  Boundary contents may move
along an authored equation, but their source/target type and support fibre may
not change. -/
inductive SameFiber {source : CIGSLT} :
    CostStaticChoiceOccurrence source →
      CostStaticChoiceOccurrence source → Prop where
  | application (firstPosition secondPosition : OneHoleContext)
      (sourceLabel : String) (firstArguments secondArguments : List Pattern)
      (constructor : source.DeclaredCostConstructor) :
      SameFiber (.application firstPosition sourceLabel firstArguments constructor)
        (.application secondPosition sourceLabel secondArguments constructor)
  | collection (firstPosition secondPosition : OneHoleContext)
      (collectionType : CollType) (firstElements secondElements : List Pattern)
      (firstRest secondRest : Option String)
      (choice : CostCollectionTypingChoice) :
      SameFiber
        (.collection firstPosition collectionType firstElements firstRest choice)
        (.collection secondPosition collectionType secondElements secondRest choice)
  | boundaryApplication (firstPosition secondPosition : OneHoleContext)
      (constructor : source.DeclaredCostConstructor)
      {first second : CostRegionBoundary}
      (same : CostRegionBoundary.SameFiber first second) :
      SameFiber (.boundaryApplication firstPosition constructor first)
        (.boundaryApplication secondPosition constructor second)
  | boundaryCollection (firstPosition secondPosition : OneHoleContext)
      (collectionType : CollType) (choice : CostCollectionTypingChoice)
      {first second : CostRegionBoundary}
      (same : CostRegionBoundary.SameFiber first second) :
      SameFiber (.boundaryCollection firstPosition collectionType choice first)
        (.boundaryCollection secondPosition collectionType choice second)

/-- A retained choice is the cause attached to one exact finite boundary
record.  Non-boundary declaration choices do not match. -/
def MatchesBoundary {source : CIGSLT} :
    CostStaticChoiceOccurrence source → CostRegionBoundary → Prop
  | .boundaryApplication _ _ stored, boundary => stored = boundary
  | .boundaryCollection _ _ _ stored, boundary => stored = boundary
  | _, _ => False

@[refl]
theorem sameFiber_refl {source : CIGSLT}
    (occurrence : CostStaticChoiceOccurrence source) :
    SameFiber occurrence occurrence := by
  cases occurrence with
  | application position sourceLabel arguments constructor =>
      exact .application position position sourceLabel arguments arguments
        constructor
  | collection position collectionType elements rest choice =>
      exact .collection position position collectionType elements elements rest
        rest choice
  | boundaryApplication position constructor boundary =>
      exact .boundaryApplication position position constructor
        (CostRegionBoundary.sameFiber_refl boundary)
  | boundaryCollection position collectionType choice boundary =>
      exact .boundaryCollection position position collectionType choice
        (CostRegionBoundary.sameFiber_refl boundary)

@[symm]
theorem SameFiber.symm {source : CIGSLT}
    {first second : CostStaticChoiceOccurrence source}
    (same : SameFiber first second) : SameFiber second first := by
  cases same with
  | application firstPosition secondPosition sourceLabel firstArguments
      secondArguments constructor =>
      exact .application secondPosition firstPosition sourceLabel secondArguments
        firstArguments constructor
  | collection firstPosition secondPosition collectionType firstElements
      secondElements firstRest secondRest choice =>
      exact .collection secondPosition firstPosition collectionType secondElements
        firstElements secondRest firstRest choice
  | boundaryApplication firstPosition secondPosition constructor boundarySame =>
      exact .boundaryApplication secondPosition firstPosition constructor
        boundarySame.symm
  | boundaryCollection firstPosition secondPosition collectionType choice
      boundarySame =>
      exact .boundaryCollection secondPosition firstPosition collectionType choice
        boundarySame.symm

@[trans]
theorem SameFiber.trans {source : CIGSLT}
    {first middle last : CostStaticChoiceOccurrence source}
    (firstMiddle : SameFiber first middle)
    (middleLast : SameFiber middle last) : SameFiber first last := by
  cases firstMiddle with
  | application firstPosition middlePosition sourceLabel firstArguments
      middleArguments constructor =>
      cases middleLast with
      | application _ lastPosition _ _ lastArguments _ =>
          exact .application firstPosition lastPosition sourceLabel firstArguments
            lastArguments constructor
  | collection firstPosition middlePosition collectionType firstElements
      middleElements firstRest middleRest choice =>
      cases middleLast with
      | collection _ lastPosition _ _ lastElements _ lastRest _ =>
          exact .collection firstPosition lastPosition collectionType firstElements
            lastElements firstRest lastRest choice
  | boundaryApplication firstPosition middlePosition constructor firstBoundary =>
      cases middleLast with
      | boundaryApplication _ lastPosition _ secondBoundary =>
          exact .boundaryApplication firstPosition lastPosition constructor
            (firstBoundary.trans secondBoundary)
  | boundaryCollection firstPosition middlePosition collectionType choice
      firstBoundary =>
      cases middleLast with
      | boundaryCollection _ lastPosition _ _ secondBoundary =>
          exact .boundaryCollection firstPosition lastPosition collectionType
            choice
            (firstBoundary.trans secondBoundary)

end CostStaticChoiceOccurrence

mutual
  /-- Source-relative preorder inventory rooted at an explicit source
  context.  Generated Cost wire contexts stored in `decoration.outer` are not
  reused here: they inhabit a different syntax and are meaningful only at the
  compact boundary. -/
  def CostStaticPlanDecoration.choiceOccurrencesAt {source : CIGSLT} :
      CostStaticPlanDecoration source → OneHoleContext →
        List (CostStaticChoiceOccurrence source)
    | .mk _ _ _ _ _ _ _ node, position =>
        node.choiceOccurrencesAt position

  /-- Retained choices at one source-skeleton node, followed by its ordered
  source-skeleton children. -/
  def CostStaticPlanDecorationNode.choiceOccurrencesAt {source : CIGSLT} :
      CostStaticPlanDecorationNode source → OneHoleContext →
        List (CostStaticChoiceOccurrence source)
    | .bvar _, _ | .fvar _, _ => []
    | .boundaryApplication constructor boundary, position =>
        [.boundaryApplication position constructor boundary]
    | .application sourceLabel constructor children, position =>
        .application position sourceLabel
            (children.map CostStaticPlanDecoration.abstractPattern) constructor ::
          CostStaticPlanDecoration.choiceOccurrencesApplyAt children position
            sourceLabel []
    | .lambda binder body, position =>
        body.choiceOccurrencesAt
          (position.comp (.lambda binder .hole))
    | .multiLambda arity binders body, position =>
        body.choiceOccurrencesAt
          (position.comp (.multiLambda arity binders .hole))
    | .collection collectionType sourceRest choice children, position =>
        .collection position collectionType
            (children.map CostStaticPlanDecoration.abstractPattern) sourceRest
              choice ::
          CostStaticPlanDecoration.choiceOccurrencesCollectionAt children
            position collectionType [] sourceRest
    | .boundaryCollection collectionType choice boundary, position =>
        [.boundaryCollection position collectionType choice boundary]

  /-- Source-relative positions for an authored application spine. -/
  def CostStaticPlanDecoration.choiceOccurrencesApplyAt {source : CIGSLT} :
      List (CostStaticPlanDecoration source) → OneHoleContext → String →
        List Pattern → List (CostStaticChoiceOccurrence source)
    | [], _, _, _ => []
    | head :: tail, position, sourceLabel, before =>
        head.choiceOccurrencesAt
            (position.comp (.apply sourceLabel before .hole
              (tail.map CostStaticPlanDecoration.abstractPattern))) ++
          CostStaticPlanDecoration.choiceOccurrencesApplyAt tail position
            sourceLabel (before ++ [head.abstractPattern])

  /-- Source-relative positions for an authored collection spine. -/
  def CostStaticPlanDecoration.choiceOccurrencesCollectionAt
      {source : CIGSLT} :
      List (CostStaticPlanDecoration source) → OneHoleContext → CollType →
        List Pattern → Option String →
          List (CostStaticChoiceOccurrence source)
    | [], _, _, _, _ => []
    | head :: tail, position, collectionType, before, sourceRest =>
        head.choiceOccurrencesAt
            (position.comp (.collection collectionType before .hole
              (tail.map CostStaticPlanDecoration.abstractPattern) sourceRest)) ++
          CostStaticPlanDecoration.choiceOccurrencesCollectionAt tail position
            collectionType (before ++ [head.abstractPattern]) sourceRest
end

/-- Ordered declaration/collection inventory in coordinates of the exact
source skeleton used by authored equations. -/
def CostStaticPlanDecoration.choiceOccurrences {source : CIGSLT}
    (decoration : CostStaticPlanDecoration source) :
    List (CostStaticChoiceOccurrence source) :=
  decoration.choiceOccurrencesAt .hole

mutual
  /-- Every source-relative occurrence emitted by a decoration reconstructs
  the exact enclosing source skeleton. -/
  theorem CostStaticPlanDecoration.choiceOccurrencesAt_fill
      {source : CIGSLT} (decoration : CostStaticPlanDecoration source)
      (position : OneHoleContext)
      {occurrence : CostStaticChoiceOccurrence source}
      (membership : occurrence ∈ decoration.choiceOccurrencesAt position) :
      occurrence.position.fill occurrence.sitePattern =
        position.fill decoration.abstractPattern := by
    cases decoration with
    | mk sourceBound targetBound sourceAvailable compactOuter pattern sourceType
        boundaries node =>
        simpa [CostStaticPlanDecoration.choiceOccurrencesAt,
          CostStaticPlanDecoration.abstractPattern] using
            node.choiceOccurrencesAt_fill position membership

  /-- Node-local companion to `choiceOccurrencesAt_fill`. -/
  theorem CostStaticPlanDecorationNode.choiceOccurrencesAt_fill
      {source : CIGSLT} (node : CostStaticPlanDecorationNode source)
      (position : OneHoleContext)
      {occurrence : CostStaticChoiceOccurrence source}
      (membership : occurrence ∈ node.choiceOccurrencesAt position) :
      occurrence.position.fill occurrence.sitePattern =
        position.fill node.abstractPattern := by
    cases node with
    | bvar sourceIndex =>
        simp [CostStaticPlanDecorationNode.choiceOccurrencesAt] at membership
    | fvar sourceName =>
        simp [CostStaticPlanDecorationNode.choiceOccurrencesAt] at membership
    | boundaryApplication constructor boundary =>
        simp only [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          List.mem_singleton] at membership
        subst occurrence
        simp [CostStaticChoiceOccurrence.position,
          CostStaticChoiceOccurrence.sitePattern,
          CostStaticPlanDecorationNode.abstractPattern]
    | application sourceLabel constructor children =>
        simp only [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          List.mem_cons] at membership
        rcases membership with rfl | nested
        · simp [CostStaticChoiceOccurrence.position,
            CostStaticChoiceOccurrence.sitePattern,
            CostStaticPlanDecorationNode.abstractPattern]
        · simpa [CostStaticPlanDecorationNode.abstractPattern] using
            CostStaticPlanDecoration.choiceOccurrencesApplyAt_fill children
              position sourceLabel [] nested
    | lambda binder body =>
        simpa [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          CostStaticPlanDecorationNode.abstractPattern,
          OneHoleContext.fill_comp, OneHoleContext.fill] using
            body.choiceOccurrencesAt_fill
              (position.comp (.lambda binder .hole)) membership
    | multiLambda arity binders body =>
        simpa [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          CostStaticPlanDecorationNode.abstractPattern,
          OneHoleContext.fill_comp, OneHoleContext.fill] using
            body.choiceOccurrencesAt_fill
              (position.comp (.multiLambda arity binders .hole)) membership
    | collection collectionType sourceRest choice children =>
        simp only [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          List.mem_cons] at membership
        rcases membership with rfl | nested
        · simp [CostStaticChoiceOccurrence.position,
            CostStaticChoiceOccurrence.sitePattern,
            CostStaticPlanDecorationNode.abstractPattern]
        · simpa [CostStaticPlanDecorationNode.abstractPattern] using
            CostStaticPlanDecoration.choiceOccurrencesCollectionAt_fill children
              position collectionType [] sourceRest nested
    | boundaryCollection collectionType choice boundary =>
        simp only [CostStaticPlanDecorationNode.choiceOccurrencesAt,
          List.mem_singleton] at membership
        subst occurrence
        simp [CostStaticChoiceOccurrence.position,
          CostStaticChoiceOccurrence.sitePattern,
          CostStaticPlanDecorationNode.abstractPattern]

  /-- Application-spine companion: the `before` prefix and remaining
  decorations reconstruct the exact authored application. -/
  theorem CostStaticPlanDecoration.choiceOccurrencesApplyAt_fill
      {source : CIGSLT} (children : List (CostStaticPlanDecoration source))
      (position : OneHoleContext) (sourceLabel : String)
      (before : List Pattern)
      {occurrence : CostStaticChoiceOccurrence source}
      (membership : occurrence ∈
        CostStaticPlanDecoration.choiceOccurrencesApplyAt children position
          sourceLabel before) :
      occurrence.position.fill occurrence.sitePattern =
        position.fill (.apply sourceLabel
          (before ++ children.map CostStaticPlanDecoration.abstractPattern)) := by
    cases children with
    | nil =>
        simp [CostStaticPlanDecoration.choiceOccurrencesApplyAt] at membership
    | cons head tail =>
        simp only [CostStaticPlanDecoration.choiceOccurrencesApplyAt,
          List.mem_append] at membership
        rcases membership with inHead | inTail
        · have selected := head.choiceOccurrencesAt_fill
            (position.comp (.apply sourceLabel before .hole
              (tail.map CostStaticPlanDecoration.abstractPattern))) inHead
          simpa [OneHoleContext.fill_comp, OneHoleContext.fill,
            List.append_assoc] using selected
        · have selected :=
            CostStaticPlanDecoration.choiceOccurrencesApplyAt_fill tail position
              sourceLabel (before ++ [head.abstractPattern]) inTail
          simpa [List.append_assoc] using selected

  /-- Collection-spine companion: source collection kind, order, and optional
  tail are all retained while child contents may evolve. -/
  theorem CostStaticPlanDecoration.choiceOccurrencesCollectionAt_fill
      {source : CIGSLT} (children : List (CostStaticPlanDecoration source))
      (position : OneHoleContext) (collectionType : CollType)
      (before : List Pattern) (sourceRest : Option String)
      {occurrence : CostStaticChoiceOccurrence source}
      (membership : occurrence ∈
        CostStaticPlanDecoration.choiceOccurrencesCollectionAt children position
          collectionType before sourceRest) :
      occurrence.position.fill occurrence.sitePattern =
        position.fill (.collection collectionType
          (before ++ children.map CostStaticPlanDecoration.abstractPattern)
            sourceRest) := by
    cases children with
    | nil =>
        simp [CostStaticPlanDecoration.choiceOccurrencesCollectionAt] at membership
    | cons head tail =>
        simp only [CostStaticPlanDecoration.choiceOccurrencesCollectionAt,
          List.mem_append] at membership
        rcases membership with inHead | inTail
        · have selected := head.choiceOccurrencesAt_fill
            (position.comp (.collection collectionType before .hole
              (tail.map CostStaticPlanDecoration.abstractPattern) sourceRest))
                inHead
          simpa [OneHoleContext.fill_comp, OneHoleContext.fill,
            List.append_assoc] using selected
        · have selected :=
            CostStaticPlanDecoration.choiceOccurrencesCollectionAt_fill tail
              position collectionType (before ++ [head.abstractPattern])
                sourceRest inTail
          simpa [List.append_assoc] using selected
end

/-- Every retained choice is an actual, exact occurrence of its site pattern
in the source skeleton.  This rules out fabricated positions before generator
provenance is considered. -/
theorem CostStaticPlanDecoration.choiceOccurrence_selects
    {source : CIGSLT} (decoration : CostStaticPlanDecoration source)
    {occurrence : CostStaticChoiceOccurrence source}
    (membership : occurrence ∈ decoration.choiceOccurrences) :
    Selects occurrence.sitePattern occurrence.position
      decoration.abstractPattern := by
  have filled : occurrence.position.fill occurrence.sitePattern =
      decoration.abstractPattern := by
    simpa [CostStaticPlanDecoration.choiceOccurrences] using
      decoration.choiceOccurrencesAt_fill .hole membership
  rw [← filled]
  exact Selects.of_fill occurrence.position occurrence.sitePattern

/-- Partial contravariant origins for retained static-plan choices.

An authored equation may introduce or delete constructors in its own redex
template, so target choices do not in general form a total pullback to source
choices.  `none` records an authored target-side occurrence; `some i` records
a residual of source occurrence `i`.  Duplication and discarding remain
possible, while every claimed residual preserves its exact declaration or
collection identity and boundary fibre. -/
structure CostStaticChoiceOriginMap (source : CIGSLT)
    (sourceChoices targetChoices :
      List (CostStaticChoiceOccurrence source)) where
  origin : Fin targetChoices.length → Option (Fin sourceChoices.length)
  preservesFiber : ∀ targetIndex sourceIndex,
    origin targetIndex = some sourceIndex →
    CostStaticChoiceOccurrence.SameFiber
      (sourceChoices.get sourceIndex)
      (targetChoices.get targetIndex)

namespace CostStaticChoiceOriginMap

/-- Identity gives every target occurrence its identical source origin. -/
def identity {source : CIGSLT}
    (choices : List (CostStaticChoiceOccurrence source)) :
    CostStaticChoiceOriginMap source choices choices where
  origin := fun index => some index
  preservesFiber := by
    intro targetIndex sourceIndex equality
    cases Option.some.inj equality
    exact CostStaticChoiceOccurrence.sameFiber_refl (choices.get targetIndex)

/-- Compose partial origins.  A target introduced by the second step remains
introduced; a residual survives only when both origin links exist. -/
def comp {source : CIGSLT}
    {first middle last : List (CostStaticChoiceOccurrence source)}
    (firstToMiddle : CostStaticChoiceOriginMap source first middle)
    (middleToLast : CostStaticChoiceOriginMap source middle last) :
    CostStaticChoiceOriginMap source first last where
  origin := fun index =>
    (middleToLast.origin index).bind firstToMiddle.origin
  preservesFiber := by
    intro targetIndex sourceIndex composite
    cases middleEquality : middleToLast.origin targetIndex with
    | none => simp [middleEquality] at composite
    | some middleIndex =>
        have sourceEquality : firstToMiddle.origin middleIndex =
            some sourceIndex := by
          simpa [middleEquality] using composite
        exact (firstToMiddle.preservesFiber middleIndex sourceIndex
          sourceEquality).trans
            (middleToLast.preservesFiber targetIndex middleIndex
              middleEquality)

/-- Retained-choice origin transport is determined by its finite partial
origin function; the fibre law is proposition-valued. -/
@[ext]
theorem ext {source : CIGSLT}
    {sourceChoices targetChoices :
      List (CostStaticChoiceOccurrence source)}
    {first second : CostStaticChoiceOriginMap source sourceChoices
      targetChoices}
    (origin_eq : first.origin = second.origin) : first = second := by
  cases first
  cases second
  cases origin_eq
  rfl

@[simp]
theorem identity_comp {source : CIGSLT}
    {first last : List (CostStaticChoiceOccurrence source)}
    (transport : CostStaticChoiceOriginMap source first last) :
    comp (identity first) transport = transport := by
  apply ext
  funext index
  simp [comp, identity]

@[simp]
theorem comp_identity {source : CIGSLT}
    {first last : List (CostStaticChoiceOccurrence source)}
    (transport : CostStaticChoiceOriginMap source first last) :
    comp transport (identity last) = transport := by
  apply ext
  funext index
  simp [comp, identity]

@[simp]
theorem comp_assoc {source : CIGSLT}
    {first second third fourth :
      List (CostStaticChoiceOccurrence source)}
    (firstSecond : CostStaticChoiceOriginMap source first second)
    (secondThird : CostStaticChoiceOriginMap source second third)
    (thirdFourth : CostStaticChoiceOriginMap source third fourth) :
    comp (comp firstSecond secondThird) thirdFourth =
      comp firstSecond (comp secondThird thirdFourth) := by
  apply ext
  funext index
  simp [comp, Option.bind_assoc]

/-- A partial origin map from an empty source has no residual occurrences.
Target choices may still be introduced by the exact authored generator. -/
theorem origin_eq_none_of_source_empty {source : CIGSLT}
    {targetChoices : List (CostStaticChoiceOccurrence source)}
    (transport : CostStaticChoiceOriginMap source [] targetChoices)
    (targetIndex : Fin targetChoices.length) :
    transport.origin targetIndex = none := by
  cases equality : transport.origin targetIndex with
  | none => rfl
  | some sourceIndex => exact Fin.elim0 sourceIndex

/-- The all-introduced partial map is valid at the occurrence layer.  An
actual semantic edge must separately prove that its exact authored generator
owns these target-side occurrences. -/
def introduceAll {source : CIGSLT}
    (targetChoices : List (CostStaticChoiceOccurrence source)) :
    CostStaticChoiceOriginMap source [] targetChoices where
  origin := fun _ => none
  preservesFiber := by simp

end CostStaticChoiceOriginMap


namespace CostStaticChoiceOccurrence

/-- Exact authored origin for a target-side choice with no residual source
occurrence.

Only literal application nodes of a selected equation orientation can be new.
An application copied from a metavariable binding remains residual, and bare
collections, recursive boundaries, and reflective equality do not acquire an
ambient creation privilege.  Symmetric closure still permits a collapsing
edge to be traversed in reverse; it does not require a second primitive edge
that recreates discarded evidence. -/
inductive IntroducedByGenerator {source : CIGSLT} :
    ∀ {left right : Pattern},
      EquationSemantics.AuthoredGeneratorWitness
          defaultBasePremises
          source.theory.presentation.presentation.language left right →
        CostStaticChoiceOccurrence source → Prop where
  | equation (context : OneHoleContext) {redex contractum : Pattern}
      (instanceWitness : EquationSemantics.AuthoredEquationInstanceWitness
        defaultBasePremises source.theory.presentation.presentation.language
        redex contractum)
      {relative : OneHoleContext} {sourceLabel : String}
      {arguments : List Pattern}
      {constructor : source.DeclaredCostConstructor}
      (template :
        EquationSemantics.AuthoredEquationInstanceWitness.TargetApplicationTemplate
        instanceWitness relative sourceLabel arguments) :
      IntroducedByGenerator
        (EquationSemantics.AuthoredGeneratorWitness.equation context
          instanceWitness)
        (.application (context.comp relative) sourceLabel arguments constructor)

/-- The exact template witness selects the claimed occurrence in the target
endpoint of the authored generator. -/
theorem IntroducedByGenerator.selects {source : CIGSLT}
    {left right : Pattern}
    {generator : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.theory.presentation.presentation.language
      left right}
    {occurrence : CostStaticChoiceOccurrence source}
    (introduced : IntroducedByGenerator generator occurrence) :
    Selects occurrence.sitePattern occurrence.position right := by
  cases introduced with
  | @equation context redex contractum instanceWitness relative sourceLabel
      arguments constructor template =>
      have selected := template.selects
      have filled :
          (context.comp relative).fill (.apply sourceLabel arguments) =
            context.fill contractum := by
        rw [OneHoleContext.fill_comp, selected.fill_eq]
      rw [← filled]
      exact Selects.of_fill (context.comp relative)
        (.apply sourceLabel arguments)

/-- Exact template introduction is, in particular, inside the redex selected
by the contextual equation generator. -/
theorem IntroducedByGenerator.inRedex {source : CIGSLT}
    {left right : Pattern}
    {generator : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.theory.presentation.presentation.language
      left right}
    {occurrence : CostStaticChoiceOccurrence source}
    (introduced : IntroducedByGenerator generator occurrence) :
    ∃ inner : OneHoleContext,
      occurrence.position = generator.redexContext.comp inner := by
  cases introduced with
  | equation context instanceWitness template =>
      exact ⟨_, rfl⟩

/-- A newly authored choice necessarily belongs to an equation occurrence;
reflective witnesses have no creation constructor. -/
theorem IntroducedByGenerator.generator_isEquation {source : CIGSLT}
    {left right : Pattern}
    {generator : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.theory.presentation.presentation.language
      left right}
    {occurrence : CostStaticChoiceOccurrence source}
    (introduced : IntroducedByGenerator generator occurrence) :
    generator.isEquation = true := by
  cases introduced
  rfl

/-- Negative canary: reflective equality can rearrange or discard retained
choices, but it cannot be cited as the primitive origin of a newly minted
choice. -/
theorem not_introducedByGenerator_reflective {source : CIGSLT}
    (context : OneHoleContext) {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (membership : declaration ∈
      source.theory.presentation.presentation.language.reflectivePresentations)
    (representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration right)
    (occurrence : CostStaticChoiceOccurrence source) :
    ¬ IntroducedByGenerator
      (EquationSemantics.AuthoredGeneratorWitness.reflective context
        ⟨declaration, membership⟩ representatives) occurrence := by
  intro introduced
  have equation := introduced.generator_isEquation
  simp [EquationSemantics.AuthoredGeneratorWitness.isEquation] at equation

/-- A retained choice lies in the redex zone of an exact authored contextual
generator.  Choices outside this zone belong to the unchanged context and
must have residual origins; choices inside may be introduced or removed by
the authored rule template. -/
def InRedex {source : CIGSLT} {left right : Pattern}
    (generator : EquationSemantics.AuthoredGeneratorWitness
      defaultBasePremises source.theory.presentation.presentation.language
      left right)
    (occurrence : CostStaticChoiceOccurrence source) : Prop :=
  ∃ inner : OneHoleContext,
    occurrence.position = generator.redexContext.comp inner

end CostStaticChoiceOccurrence

/-- The semantic kernel used by recursive Cost-decoration transport.

`Edge` is Type-valued so its authored generator identity and finite occurrence
map remain data tied to the edge rather than separately supplied proof
parameters.  Forgetting that data recovers the proposition-valued equation
semantics.  A concrete object supplies only edges whose declaration/collection
choices are transported by its ordered canonical-key presentation; there is
intentionally no generic default that would admit arbitrary choice changes.

Every edge projects to one generator of the sole authored source theory.  Its
boundary lists must be exactly the lists stored by the two plan decorations,
and its boundary pullback is the map used by recursive child transport.

Constructor choices use partial origins rather than a total pullback.  Every
residual preserves exact declaration/collection identity; every target with
no source origin must be the instantiated image of a literal application in
the selected authored equation orientation.  Choices in the unchanged context
are covered in both directions.  This distinction is essential for ordinary
unit/associativity laws, whose templates genuinely introduce or delete
constructor occurrences. -/
structure CostStaticPlanLift (source : CIGSLT) where
  Edge : (first second : CostStaticPlanDecoration source) →
    (sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)) → Type
  preservesFiber : ∀ {first second sourceBoundaries targetBoundaries},
    Edge first second sourceBoundaries targetBoundaries →
      CostStaticPlanDecoration.SameFiber first second
  generatorWitness :
    ∀ {first second sourceBoundaries targetBoundaries},
      Edge first second sourceBoundaries targetBoundaries →
        EquationSemantics.AuthoredGeneratorWitness
          defaultBasePremises source.theory.presentation.presentation.language
          first.abstractPattern second.abstractPattern
  sourceBoundaries_eq :
    ∀ {first second sourceBoundaries targetBoundaries},
      Edge first second sourceBoundaries targetBoundaries →
        first.boundaries =
          sourceBoundaries.map (fun boundary => boundary.1)
  targetBoundaries_eq :
    ∀ {first second sourceBoundaries targetBoundaries},
      Edge first second sourceBoundaries targetBoundaries →
        second.boundaries =
          targetBoundaries.map (fun boundary => boundary.1)
  boundaryMap : ∀ {first second sourceBoundaries targetBoundaries},
    Edge first second sourceBoundaries targetBoundaries →
      CostBoundaryFiberMap source sourceBoundaries targetBoundaries
  choiceOrigins : ∀ {first second sourceBoundaries targetBoundaries},
    Edge first second sourceBoundaries targetBoundaries →
      CostStaticChoiceOriginMap source first.choiceOccurrences
        second.choiceOccurrences
  introducedChoice :
    ∀ {first second sourceBoundaries targetBoundaries}
      (edge : Edge first second sourceBoundaries targetBoundaries)
      (targetIndex : Fin second.choiceOccurrences.length),
      (choiceOrigins edge).origin targetIndex = none →
        CostStaticChoiceOccurrence.IntroducedByGenerator
          (generatorWitness edge)
          (second.choiceOccurrences.get targetIndex)
  sourceContextChoiceCovered :
    ∀ {first second sourceBoundaries targetBoundaries}
      (edge : Edge first second sourceBoundaries targetBoundaries)
      (sourceIndex : Fin first.choiceOccurrences.length),
      ¬ CostStaticChoiceOccurrence.InRedex
          (generatorWitness edge)
          (first.choiceOccurrences.get sourceIndex) →
      ∃ targetIndex : Fin second.choiceOccurrences.length,
        (choiceOrigins edge).origin targetIndex = some sourceIndex ∧
          (first.choiceOccurrences.get sourceIndex).position =
            (second.choiceOccurrences.get targetIndex).position
  boundaryChoiceCoherent :
    ∀ {first second sourceBoundaries targetBoundaries}
      (edge : Edge first second sourceBoundaries targetBoundaries)
      (targetIndex : Fin targetBoundaries.length),
      ∃ targetChoiceIndex : Fin second.choiceOccurrences.length,
        ∃ sourceChoiceIndex : Fin first.choiceOccurrences.length,
        CostStaticChoiceOccurrence.MatchesBoundary
            (second.choiceOccurrences.get targetChoiceIndex)
            (targetBoundaries.get targetIndex).1 ∧
          (choiceOrigins edge).origin targetChoiceIndex =
            some sourceChoiceIndex ∧
          CostStaticChoiceOccurrence.MatchesBoundary
            (first.choiceOccurrences.get sourceChoiceIndex)
            (sourceBoundaries.get
              ((boundaryMap edge).pullback targetIndex)).1

namespace CostStaticPlanLift

/-- Forget a plan edge's proof-relevant authored occurrence and recover the
ordinary source equation generator. -/
def erasesToSourceGenerator {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries) :
    EquationSemantics.EquationContextStep defaultBasePremises
      source.theory.presentation.presentation.language
      first.abstractPattern second.abstractPattern :=
  (staticLift.generatorWitness edge).erase

/-- Map the exact source occurrence carried by a plan edge into one selected
static Cost colour.  This retains declaration, orientation, bindings, and
redex context as data; it does not search the generated equation table for an
unrelated edge with the same endpoints. -/
def mappedGeneratorWitness {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    (color : CostStaticColor)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries) :
    EquationSemantics.AuthoredGeneratorWitness defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) first.abstractPattern)
      (mapPattern (color.symbols source) second.abstractPattern) :=
  (staticLift.generatorWitness edge).mapCostStatic source color

/-- Forgetting the mapped plan occurrence is exactly the old support-level
Cost map applied to the very same source occurrence. -/
theorem mappedGeneratorWitness_erase {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    (color : CostStaticColor)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries) :
    (staticLift.mappedGeneratorWitness color edge).erase =
      equationContextStep_mapCostStatic source color
        (staticLift.erasesToSourceGenerator edge) :=
  EquationSemantics.AuthoredGeneratorWitness.erase_mapCostStatic
    source color (staticLift.generatorWitness edge)

/-- Exact template provenance implies the coarser positional redex fact. -/
theorem introducedChoiceInRedex {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length)
    (introduced : (staticLift.choiceOrigins edge).origin targetIndex = none) :
    CostStaticChoiceOccurrence.InRedex
      (staticLift.generatorWitness edge)
      (second.choiceOccurrences.get targetIndex) :=
  (staticLift.introducedChoice edge targetIndex introduced).inRedex

end CostStaticPlanLift

/-- One fully witnessed lawful edge between static-plan decorations.

This is the concrete maximal edge type: it stores the exact proof-relevant
authored generator, finite boundary pullback, partial constructor origins,
unchanged-context coverage, and boundary/choice coherence.  In particular,
the edge is not an opaque callback and cannot be inhabited merely by
presenting two endpoint patterns. -/
structure CostStaticPlanEdge (source : CIGSLT)
    (first second : CostStaticPlanDecoration source)
    (sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)) where
  sameFiber : CostStaticPlanDecoration.SameFiber first second
  generatorWitness : EquationSemantics.AuthoredGeneratorWitness
    defaultBasePremises source.theory.presentation.presentation.language
      first.abstractPattern second.abstractPattern
  sourceBoundaryInventory : first.boundaries =
    sourceBoundaries.map (fun boundary => boundary.1)
  targetBoundaryInventory : second.boundaries =
    targetBoundaries.map (fun boundary => boundary.1)
  boundaryOrigins :
    CostBoundaryFiberMap source sourceBoundaries targetBoundaries
  choiceOrigins : CostStaticChoiceOriginMap source first.choiceOccurrences
    second.choiceOccurrences
  introducedChoice :
    ∀ (targetIndex : Fin second.choiceOccurrences.length),
      choiceOrigins.origin targetIndex = none →
        CostStaticChoiceOccurrence.IntroducedByGenerator generatorWitness
          (second.choiceOccurrences.get targetIndex)
  sourceContextChoiceCovered :
    ∀ (sourceIndex : Fin first.choiceOccurrences.length),
      ¬ CostStaticChoiceOccurrence.InRedex generatorWitness
          (first.choiceOccurrences.get sourceIndex) →
      ∃ targetIndex : Fin second.choiceOccurrences.length,
        choiceOrigins.origin targetIndex = some sourceIndex ∧
          (first.choiceOccurrences.get sourceIndex).position =
            (second.choiceOccurrences.get targetIndex).position
  boundaryChoiceCoherent :
    ∀ (targetIndex : Fin targetBoundaries.length),
      ∃ targetChoiceIndex : Fin second.choiceOccurrences.length,
        ∃ sourceChoiceIndex : Fin first.choiceOccurrences.length,
          CostStaticChoiceOccurrence.MatchesBoundary
              (second.choiceOccurrences.get targetChoiceIndex)
              (targetBoundaries.get targetIndex).1 ∧
            choiceOrigins.origin targetChoiceIndex = some sourceChoiceIndex ∧
            CostStaticChoiceOccurrence.MatchesBoundary
              (first.choiceOccurrences.get sourceChoiceIndex)
              (sourceBoundaries.get
                (boundaryOrigins.pullback targetIndex)).1

namespace CostStaticPlanEdge

/-- Every source choice named by a lawful edge selects its exact site in the
source endpoint.  This is a derived fact of the decoration inventory, not an
extra field that an edge author may assert. -/
theorem sourceChoice_selects {source : CIGSLT}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (_edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    (sourceIndex : Fin first.choiceOccurrences.length) :
    Selects (first.choiceOccurrences.get sourceIndex).sitePattern
      (first.choiceOccurrences.get sourceIndex).position
      first.abstractPattern := by
  exact first.choiceOccurrence_selects
    (List.get_mem first.choiceOccurrences sourceIndex)

/-- Every target choice named by a lawful edge selects its exact site in the
target endpoint.  Together with `sourceChoice_selects`, this prevents an
occurrence map from assigning provenance to fabricated coordinates. -/
theorem targetChoice_selects {source : CIGSLT}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (_edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length) :
    Selects (second.choiceOccurrences.get targetIndex).sitePattern
      (second.choiceOccurrences.get targetIndex).position
      second.abstractPattern := by
  exact second.choiceOccurrence_selects
    (List.get_mem second.choiceOccurrences targetIndex)

end CostStaticPlanEdge

namespace CIGSLT

/-- The canonical static-plan lift is the maximal relation consisting of
fully witnessed lawful edges.  Objects do not get to choose a more permissive
hidden relation; later constructions must produce the concrete occurrence
evidence recorded by `CostStaticPlanEdge`. -/
def costStaticPlanLift (source : CIGSLT) : CostStaticPlanLift source where
  Edge := CostStaticPlanEdge source
  preservesFiber := CostStaticPlanEdge.sameFiber
  generatorWitness := CostStaticPlanEdge.generatorWitness
  sourceBoundaries_eq := CostStaticPlanEdge.sourceBoundaryInventory
  targetBoundaries_eq := CostStaticPlanEdge.targetBoundaryInventory
  boundaryMap := CostStaticPlanEdge.boundaryOrigins
  choiceOrigins := CostStaticPlanEdge.choiceOrigins
  introducedChoice := CostStaticPlanEdge.introducedChoice
  sourceContextChoiceCovered :=
    CostStaticPlanEdge.sourceContextChoiceCovered
  boundaryChoiceCoherent := CostStaticPlanEdge.boundaryChoiceCoherent

end CIGSLT

namespace CostStaticPlanLift

/-- With no target boundary, the occurrence pullback carried by an edge is
the unique empty-target map.  Discarding is explicit but needs no arbitrary
choice. -/
theorem boundaryMap_eq_discardAll {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries []) :
    staticLift.boundaryMap edge =
      CostBoundaryFiberMap.discardAll sourceBoundaries := by
  apply CostBoundaryFiberMap.ext
  funext index
  exact Fin.elim0 index

/-- No admitted static edge can create a target boundary from an empty source
family.  This lifts the finite-map negative canary to the actual object-level
edge interface. -/
theorem noCreationFromEmpty {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (targetIndex : Fin targetBoundaries.length) :
    IsEmpty (staticLift.Edge first second [] targetBoundaries) :=
  ⟨fun edge =>
    (CostBoundaryFiberMap.noCreationFromEmpty targetIndex).false
      (staticLift.boundaryMap edge)⟩

/-- If a source plan has no retained choices, every target-side choice of an
admitted edge is necessarily inside the exact authored redex.  This is the
correct replacement for a global no-creation claim: authored unit and
associativity templates may genuinely introduce constructors. -/
theorem targetChoiceInRedex_of_sourceChoices_eq_nil {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (empty : first.choiceOccurrences = [])
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length) :
    CostStaticChoiceOccurrence.InRedex
      (staticLift.generatorWitness edge)
      (second.choiceOccurrences.get targetIndex) := by
  apply staticLift.introducedChoiceInRedex edge targetIndex
  cases originEquality : (staticLift.choiceOrigins edge).origin targetIndex with
  | none => rfl
  | some sourceIndex =>
      have emptyLength : first.choiceOccurrences.length = 0 := by
        simpa using congrArg List.length empty
      have impossible := sourceIndex.isLt
      omega

/-- A target occurrence classified as newly authored selects the target
endpoint through its rule-template witness, independently of the decoration
inventory reconstruction theorem. -/
theorem targetChoice_selects_of_noOrigin {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length)
    (introduced : (staticLift.choiceOrigins edge).origin targetIndex = none) :
    Selects (second.choiceOccurrences.get targetIndex).sitePattern
      (second.choiceOccurrences.get targetIndex).position
      second.abstractPattern :=
  (staticLift.introducedChoice edge targetIndex introduced).selects

/-- Reflective generators may transport, rearrange, or discard choices, but
cannot mint one.  Hence every target choice of a reflective edge has a concrete
residual source origin. -/
theorem targetChoice_has_origin_of_reflectiveGenerator {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (reflective : (staticLift.generatorWitness edge).isEquation = false)
    (targetIndex : Fin second.choiceOccurrences.length) :
    ∃ sourceIndex : Fin first.choiceOccurrences.length,
      (staticLift.choiceOrigins edge).origin targetIndex = some sourceIndex := by
  cases origin_eq : (staticLift.choiceOrigins edge).origin targetIndex with
  | none =>
      have introduced := staticLift.introducedChoice edge targetIndex origin_eq
      have equation := introduced.generator_isEquation
      rw [reflective] at equation
      contradiction
  | some sourceIndex => exact ⟨sourceIndex, rfl⟩

/-- Negative canary: with no source choice inventory, an admitted edge cannot
place a target choice outside its authored redex.  Constructor creation is
local to the exact rule occurrence, never ambient authority. -/
theorem not_targetChoiceOutsideRedex_of_sourceChoices_eq_nil
    {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (empty : first.choiceOccurrences = [])
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length)
    (outside : ¬ CostStaticChoiceOccurrence.InRedex
      (staticLift.generatorWitness edge)
      (second.choiceOccurrences.get targetIndex)) :
    False :=
  outside (staticLift.targetChoiceInRedex_of_sourceChoices_eq_nil empty edge
    targetIndex)

/-- Every target choice in the unchanged outer context has a concrete source
origin.  Thus `none` cannot be used as a blanket escape hatch for changing
ambiguous declaration choices away from the authored redex. -/
theorem targetContextChoice_has_origin {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin second.choiceOccurrences.length)
    (outside : ¬ CostStaticChoiceOccurrence.InRedex
      (staticLift.generatorWitness edge)
      (second.choiceOccurrences.get targetIndex)) :
    ∃ sourceIndex : Fin first.choiceOccurrences.length,
      (staticLift.choiceOrigins edge).origin targetIndex = some sourceIndex := by
  cases originEquality :
      (staticLift.choiceOrigins edge).origin targetIndex with
  | none =>
      exact (outside
        (staticLift.introducedChoiceInRedex edge targetIndex
          originEquality)).elim
  | some sourceIndex => exact ⟨sourceIndex, rfl⟩

/-- Every recursive target boundary has a residual source-side declaration or
collection cause aligned with the same boundary pullback used for its child.
Rule-introduced constructors can therefore never masquerade as unexplained
recursive boundary children. -/
theorem targetBoundary_has_residualChoice {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (edge : staticLift.Edge first second sourceBoundaries targetBoundaries)
    (targetIndex : Fin targetBoundaries.length) :
    ∃ targetChoiceIndex : Fin second.choiceOccurrences.length,
      ∃ sourceChoiceIndex : Fin first.choiceOccurrences.length,
        CostStaticChoiceOccurrence.MatchesBoundary
            (second.choiceOccurrences.get targetChoiceIndex)
            (targetBoundaries.get targetIndex).1 ∧
          (staticLift.choiceOrigins edge).origin targetChoiceIndex =
            some sourceChoiceIndex ∧
          CostStaticChoiceOccurrence.MatchesBoundary
            (first.choiceOccurrences.get sourceChoiceIndex)
            (sourceBoundaries.get
              ((staticLift.boundaryMap edge).pullback targetIndex)).1 :=
  staticLift.boundaryChoiceCoherent edge targetIndex

/-- A target boundary without a retained boundary-cause occurrence cannot be
admitted.  This is the negative canary tying the recursive child pullback to
the declaration/collection-choice residual origin. -/
theorem noTargetBoundaryWithoutChoice {source : CIGSLT}
    (staticLift : CostStaticPlanLift source)
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    (empty : second.choiceOccurrences = [])
    (targetIndex : Fin targetBoundaries.length) :
    IsEmpty (staticLift.Edge first second sourceBoundaries
      targetBoundaries) :=
  ⟨fun edge => by
    obtain ⟨choiceIndex, _sourceChoiceIndex, _targetMatch,
      _origin, _sourceMatch⟩ :=
      staticLift.boundaryChoiceCoherent edge targetIndex
    rw [empty] at choiceIndex
    exact Fin.elim0 choiceIndex⟩

end CostStaticPlanLift

/-- One actual typed child selected from a finite static-boundary forest.

The boundary record and its tree remain dependent: projecting them to a raw
pair is an observation, not the carrier used by semantic transport. -/
structure CostRegionBoundaryTreeEntry (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (color : CostStaticColor) where
  boundary : TypedCostRegionBoundary source color targetFree
  tree : CostRegionTree source targetFree boundary.boundary.targetSupport []
    boundary.boundary.content boundary.boundary.targetType

namespace CostRegionBoundaryTreeEntry

/-- Forget the typing proof of a boundary entry while retaining the complete
recursive decoration selected by its actual child tree. -/
def decoration {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    (entry : CostRegionBoundaryTreeEntry source targetFree color) :
    CostRegionBoundary × CostTreeDecoration source :=
  (entry.boundary.boundary, entry.tree.decoration)

end CostRegionBoundaryTreeEntry

namespace CostRegionBoundaryTrees

/-- Dependently select the actual typed child at an index of the projected
boundary-decoration list.  This is the bridge from a finite occurrence
pullback to the proof-relevant tree it names; no tree is reconstructed from
the projection. -/
def getDecoration {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    Fin trees.decorations.length →
      CostRegionBoundaryTreeEntry source targetFree color :=
  match trees with
  | .nil => fun index => Fin.elim0 index
  | .cons head children => fun index =>
      Fin.cases ⟨_, head⟩ (fun tailIndex => children.getDecoration tailIndex)
        index

/-- Selecting an actual boundary child and then projecting it agrees exactly
with selecting the corresponding element of the nondependent decoration
list. -/
theorem getDecoration_decoration {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    ∀ index : Fin trees.decorations.length,
      (trees.getDecoration index).decoration = trees.decorations.get index :=
  match trees with
  | .nil => fun index => Fin.elim0 index
  | .cons head children => fun index =>
      Fin.cases rfl (fun tailIndex => children.getDecoration_decoration tailIndex)
        index

end CostRegionBoundaryTrees

/-- Root identity retained by structural Cost transport.  Static regions
remember their selected colour and source sort; equation-neutral applications
remember the exact declaration and quotation mode.  Finer declaration and
collection identities inside a static stratum are governed by its supplied
`CostStaticPlanLift.Edge`. -/
inductive CostTreeRootIdentity (source : CIGSLT) where
  | bvar
  | fvar
  | static (color : CostStaticColor) (sourceSort : String)
  | neutralApplication (kind : CostNeutralFrameKind)
      (constructor : source.DeclaredCostConstructor)
  | lambda
  | multiLambda
  | subst
  | collection

def CostTreeDecoration.rootIdentity {source : CIGSLT} :
    CostTreeDecoration source → CostTreeRootIdentity source
  | .mk _ _ _ _ .bvar => .bvar
  | .mk _ _ _ _ .fvar => .fvar
  | .mk _ _ _ _ (.static color sourceSort _ _) =>
      .static color sourceSort
  | .mk _ _ _ _ (.neutralApplication kind constructor _) =>
      .neutralApplication kind constructor
  | .mk _ _ _ _ (.lambda _) => .lambda
  | .mk _ _ _ _ (.multiLambda _) => .multiLambda
  | .mk _ _ _ _ (.subst _ _) => .subst
  | .mk _ _ _ _ (.collection _) => .collection

mutual
  /-- Typed structural transport between two actual Cost region trees.

Unlike `CostTreeDecorationTransport`, this family never reconstructs typing
from a proof-erased snapshot. The two raw patterns may differ, while the real
trees retain their free context, binder split, type, declaration witnesses,
and finite boundary children. -/
  inductive CostRegionTreeTransport (source : CIGSLT)
      (staticLift : CostStaticPlanLift source)
      (targetFree : WellSorted.FreeTypeContext) :
      {leftAvailable leftOuter : List TypeExpr} →
      {leftPattern : Pattern} → {leftType : TypeExpr} →
      CostRegionTree source targetFree leftAvailable leftOuter leftPattern
          leftType →
      {rightAvailable rightOuter : List TypeExpr} →
      {rightPattern : Pattern} → {rightType : TypeExpr} →
      CostRegionTree source targetFree rightAvailable rightOuter rightPattern
          rightType → Prop where
    | refl
        {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
        (tree : CostRegionTree source targetFree available outer pattern type) :
        CostRegionTreeTransport source staticLift targetFree tree tree
    | static
        {color : CostStaticColor} {outer : List TypeExpr}
        (leftNode rightNode : CostStaticRegionNode source color targetFree)
        (leftChildren : CostRegionBoundaryTrees source targetFree color
          leftNode.finiteBoundaryTable)
        (rightChildren : CostRegionBoundaryTrees source targetFree color
          rightNode.finiteBoundaryTable)
        (sourceSortEq : leftNode.sourceSort = rightNode.sourceSort)
        (planStep : staticLift.Edge leftNode.plan.decoration
          rightNode.plan.decoration leftChildren.decorations
            rightChildren.decorations)
        (children : ∀ targetIndex,
          CostRegionTreeTransport source staticLift targetFree
            (leftChildren.getDecoration
              ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
            (rightChildren.getDecoration targetIndex).tree) :
        CostRegionTreeTransport source staticLift targetFree
          (CostRegionTree.static (outer := outer) leftNode leftChildren)
          (CostRegionTree.static (outer := outer) rightNode rightChildren)
    | neutralApplicationOrdinary
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ WellSorted.UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (ordinary : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeLanguage rule.label = false)
        (leftChildren : CostRegionArgumentTrees source targetFree available
          outer leftArguments rule.params)
        (rightChildren : CostRegionArgumentTrees source targetFree available
          outer rightArguments rule.params)
        (arguments : CostRegionArgumentTreesTransport source staticLift
          targetFree leftChildren rightChildren) :
        CostRegionTreeTransport source staticLift targetFree
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary leftChildren)
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary rightChildren)
    | neutralApplicationQuote
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ WellSorted.UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (quoted : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeLanguage rule.label = true)
        (leftChildren : CostRegionArgumentTrees source targetFree []
          (available ++ outer) leftArguments rule.params)
        (rightChildren : CostRegionArgumentTrees source targetFree []
          (available ++ outer) rightArguments rule.params)
        (arguments : CostRegionArgumentTreesTransport source staticLift
          targetFree leftChildren rightChildren) :
        CostRegionTreeTransport source staticLift targetFree
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted leftChildren)
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted rightChildren)
    | lambda
        {available outer : List TypeExpr} {binder : Option String}
        {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
        (leftTree : CostRegionTree source targetFree (domain :: available)
          outer leftBody codomain)
        (rightTree : CostRegionTree source targetFree (domain :: available)
          outer rightBody codomain)
        (body : CostRegionTreeTransport source staticLift targetFree leftTree
          rightTree) :
        CostRegionTreeTransport source staticLift targetFree
          (.lambda (binder := binder) leftTree)
          (.lambda (binder := binder) rightTree)
    | multiLambda
        {available outer : List TypeExpr} {arity : Nat}
        {binders : List String} {leftBody rightBody : Pattern}
        {domain codomain : TypeExpr}
        (leftTree : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer leftBody codomain)
        (rightTree : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer rightBody codomain)
        (body : CostRegionTreeTransport source staticLift targetFree leftTree
          rightTree) :
        CostRegionTreeTransport source staticLift targetFree
          (.multiLambda (arity := arity) (binders := binders) leftTree)
          (.multiLambda (arity := arity) (binders := binders) rightTree)
    | substBody
        {available outer : List TypeExpr}
        {leftBody rightBody replacement : Pattern}
        {domain codomain : TypeExpr}
        (leftTree : CostRegionTree source targetFree (domain :: available)
          outer leftBody codomain)
        (rightTree : CostRegionTree source targetFree (domain :: available)
          outer rightBody codomain)
        (replacementTree : CostRegionTree source targetFree available outer
          replacement domain)
        (body : CostRegionTreeTransport source staticLift targetFree leftTree
          rightTree) :
        CostRegionTreeTransport source staticLift targetFree
          (.subst leftTree replacementTree) (.subst rightTree replacementTree)
    | substReplacement
        {available outer : List TypeExpr}
        {bodyPattern leftReplacement rightReplacement : Pattern}
        {domain codomain : TypeExpr}
        (bodyTree : CostRegionTree source targetFree (domain :: available)
          outer bodyPattern codomain)
        (leftTree : CostRegionTree source targetFree available outer
          leftReplacement domain)
        (rightTree : CostRegionTree source targetFree available outer
          rightReplacement domain)
        (replacement : CostRegionTreeTransport source staticLift targetFree
          leftTree rightTree) :
        CostRegionTreeTransport source staticLift targetFree
          (.subst bodyTree leftTree) (.subst bodyTree rightTree)
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {leftElements rightElements : List Pattern} {rest : Option String}
        {elementType : TypeExpr}
        (leftChildren : CostRegionElementTrees source targetFree available outer
          leftElements elementType)
        (rightChildren : CostRegionElementTrees source targetFree available
          outer rightElements elementType)
        (elements : CostRegionElementTreesTransport source staticLift
          targetFree leftChildren rightChildren) :
        CostRegionTreeTransport source staticLift targetFree
          (.collection (collectionType := collectionType) (rest := rest)
            leftChildren)
          (.collection (collectionType := collectionType) (rest := rest)
            rightChildren)

  /-- Positional typed transport for the arguments of one fixed authored
  constructor. Parameter identity is shared; only argument patterns and
  their retained trees may move. -/
  inductive CostRegionArgumentTreesTransport (source : CIGSLT)
      (staticLift : CostStaticPlanLift source)
      (targetFree : WellSorted.FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftArguments rightArguments : List Pattern} →
      {parameters : List TermParam} →
      CostRegionArgumentTrees source targetFree available outer leftArguments
          parameters →
      CostRegionArgumentTrees source targetFree available outer rightArguments
          parameters → Prop where
    | nil {available outer : List TypeExpr} :
        CostRegionArgumentTreesTransport source staticLift targetFree
          (CostRegionArgumentTrees.nil (available := available) (outer := outer))
          (CostRegionArgumentTrees.nil (available := available) (outer := outer))
    | cons
        {available outer : List TypeExpr} {leftArgument rightArgument : Pattern}
        {leftArguments rightArguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (leftRepresentation :
          WellSorted.MatchesParameterRepresentation parameter leftArgument)
        (rightRepresentation :
          WellSorted.MatchesParameterRepresentation parameter rightArgument)
        (parameterType : WellSorted.parameterType? parameter = some expected)
        (leftHead : CostRegionTree source targetFree available outer
          leftArgument expected)
        (rightHead : CostRegionTree source targetFree available outer
          rightArgument expected)
        (leftTail : CostRegionArgumentTrees source targetFree available outer
          leftArguments parameters)
        (rightTail : CostRegionArgumentTrees source targetFree available outer
          rightArguments parameters)
        (head : CostRegionTreeTransport source staticLift targetFree leftHead
          rightHead)
        (tail : CostRegionArgumentTreesTransport source staticLift targetFree
          leftTail rightTail) :
        CostRegionArgumentTreesTransport source staticLift targetFree
          (.cons leftRepresentation parameterType leftHead leftTail)
          (.cons rightRepresentation parameterType rightHead rightTail)

  /-- Positional typed transport for homogeneous structural collections. -/
  inductive CostRegionElementTreesTransport (source : CIGSLT)
      (staticLift : CostStaticPlanLift source)
      (targetFree : WellSorted.FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftElements rightElements : List Pattern} → {elementType : TypeExpr} →
      CostRegionElementTrees source targetFree available outer leftElements
          elementType →
      CostRegionElementTrees source targetFree available outer rightElements
          elementType → Prop where
    | nil (available outer : List TypeExpr) (elementType : TypeExpr) :
        CostRegionElementTreesTransport source staticLift targetFree
          (.nil available outer elementType) (.nil available outer elementType)
    | cons
        {available outer : List TypeExpr} {leftElement rightElement : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (leftHead : CostRegionTree source targetFree available outer leftElement
          elementType)
        (rightHead : CostRegionTree source targetFree available outer
          rightElement elementType)
        (leftTail : CostRegionElementTrees source targetFree available outer
          leftElements elementType)
        (rightTail : CostRegionElementTrees source targetFree available outer
          rightElements elementType)
        (head : CostRegionTreeTransport source staticLift targetFree leftHead
          rightHead)
        (tail : CostRegionElementTreesTransport source staticLift targetFree
          leftTail rightTail) :
        CostRegionElementTreesTransport source staticLift targetFree
          (.cons leftHead leftTail) (.cons rightHead rightTail)
end

namespace CostRegionTreeTransport

/-- Typed transport itself proves that the two trees inhabit the same binder
split and result type.  This is derived from actual constructor indices; it is
not a free-standing certificate attached to a decoration. -/
theorem sameFiber {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter leftPattern
      leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (transport : CostRegionTreeTransport source staticLift targetFree left
      right) :
    leftAvailable = rightAvailable ∧ leftOuter = rightOuter ∧
      leftType = rightType := by
  cases transport with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | @static color outer leftNode rightNode leftChildren rightChildren
      sourceSortEq planStep children =>
      have typeEq :
          TypeExpr.base
              (CostStaticColor.mapLangSort source color leftNode.sourceSort).1 =
            TypeExpr.base
              (CostStaticColor.mapLangSort source color rightNode.sourceSort).1 := by
        simp only [CostStaticColor.mapLangSort_name]
        exact congrArg
          (fun name => TypeExpr.base ((color.symbols source).sort name))
          (congrArg Subtype.val sourceSortEq)
      exact ⟨(leftNode.plan.decoration_targetBound.symm.trans
          ((staticLift.preservesFiber planStep).targetBound_eq.trans
            rightNode.plan.decoration_targetBound)), rfl, typeEq⟩
  | neutralApplicationOrdinary => exact ⟨rfl, rfl, rfl⟩
  | neutralApplicationQuote => exact ⟨rfl, rfl, rfl⟩
  | lambda => exact ⟨rfl, rfl, rfl⟩
  | multiLambda => exact ⟨rfl, rfl, rfl⟩
  | substBody => exact ⟨rfl, rfl, rfl⟩
  | substReplacement => exact ⟨rfl, rfl, rfl⟩
  | collection => exact ⟨rfl, rfl, rfl⟩

/-- Typed transport retains the outer proof-relevant root identity. -/
theorem rootIdentity_eq {source : CIGSLT}
    {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter leftPattern
      leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (transport : CostRegionTreeTransport source staticLift targetFree left
      right) :
    left.decoration.rootIdentity = right.decoration.rootIdentity := by
  cases transport with
  | refl => rfl
  | @static color outer leftNode rightNode leftChildren rightChildren
      sourceSortEq planStep children =>
      simp only [CostRegionTree.decoration, CostTreeDecoration.rootIdentity]
      exact congrArg (CostTreeRootIdentity.static _)
        (congrArg Subtype.val sourceSortEq)
  | neutralApplicationOrdinary => rfl
  | neutralApplicationQuote => rfl
  | lambda => rfl
  | multiLambda => rfl
  | substBody => rfl
  | substReplacement => rfl
  | collection => rfl

end CostRegionTreeTransport

mutual
  /-- Structural transport of complete recursive Cost decorations, relative
  to the one unresolved monochromatic-plan lift.

Static boundaries use a finite pullback map, so one source child may feed
multiple target occurrences and unused source occurrences may disappear. -/
  inductive CostTreeDecorationTransport (source : CIGSLT)
      (staticLift : CostStaticPlanLift source) :
      CostTreeDecoration source → CostTreeDecoration source → Prop where
    | refl (decoration : CostTreeDecoration source) :
        CostTreeDecorationTransport source staticLift decoration decoration
    | static
        {leftPlan rightPlan : CostStaticPlanDecoration source}
        {outer : List TypeExpr} {type : TypeExpr}
        {color : CostStaticColor} {sourceSort : String}
        {leftBoundaries rightBoundaries :
          List (CostRegionBoundary × CostTreeDecoration source)}
        (planStep : staticLift.Edge leftPlan rightPlan
          leftBoundaries rightBoundaries)
        (children : ∀ targetIndex,
          CostTreeDecorationTransport source staticLift
            (leftBoundaries.get
              ((staticLift.boundaryMap planStep).pullback targetIndex)).2
            (rightBoundaries.get targetIndex).2) :
        CostTreeDecorationTransport source staticLift
          (.mk leftPlan.targetBound outer leftPlan.pattern type
            (.static color sourceSort leftPlan leftBoundaries))
          (.mk rightPlan.targetBound outer rightPlan.pattern type
            (.static color sourceSort rightPlan rightBoundaries))
    | neutralApplication
        {available outer : List TypeExpr} {type : TypeExpr}
        {leftPattern rightPattern : Pattern}
        {kind : CostNeutralFrameKind}
        {constructor : source.DeclaredCostConstructor}
        {leftArguments rightArguments : List (CostTreeDecoration source)}
        (arguments : CostTreeDecorationListTransport source staticLift
          leftArguments rightArguments) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer leftPattern type
            (.neutralApplication kind constructor leftArguments))
          (.mk available outer rightPattern type
            (.neutralApplication kind constructor rightArguments))
    | lambda
        {available outer : List TypeExpr} {binder : Option String}
        {leftBodyPattern rightBodyPattern : Pattern}
        {domain codomain : TypeExpr}
        {leftBody rightBody : CostTreeDecoration source}
        (body : CostTreeDecorationTransport source staticLift
          leftBody rightBody) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer (.lambda binder leftBodyPattern)
            (.arrow domain codomain) (.lambda leftBody))
          (.mk available outer (.lambda binder rightBodyPattern)
            (.arrow domain codomain) (.lambda rightBody))
    | multiLambda
        {available outer : List TypeExpr} {arity : Nat}
        {binders : List String}
        {leftBodyPattern rightBodyPattern : Pattern}
        {domain codomain : TypeExpr}
        {leftBody rightBody : CostTreeDecoration source}
        (body : CostTreeDecorationTransport source staticLift
          leftBody rightBody) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer
            (.multiLambda arity binders leftBodyPattern)
            (.arrow (.multiBinder domain) codomain) (.multiLambda leftBody))
          (.mk available outer
            (.multiLambda arity binders rightBodyPattern)
            (.arrow (.multiBinder domain) codomain) (.multiLambda rightBody))
    | substBody
        {available outer : List TypeExpr}
        {leftBodyPattern rightBodyPattern replacementPattern : Pattern}
        {domain codomain : TypeExpr}
        {leftBody rightBody replacement : CostTreeDecoration source}
        (body : CostTreeDecorationTransport source staticLift
          leftBody rightBody) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer (.subst leftBodyPattern replacementPattern)
            codomain (.subst leftBody replacement))
          (.mk available outer (.subst rightBodyPattern replacementPattern)
            codomain (.subst rightBody replacement))
    | substReplacement
        {available outer : List TypeExpr}
        {bodyPattern leftReplacementPattern rightReplacementPattern : Pattern}
        {domain codomain : TypeExpr}
        {body leftReplacement rightReplacement : CostTreeDecoration source}
        (replacement : CostTreeDecorationTransport source staticLift
          leftReplacement rightReplacement) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer (.subst bodyPattern leftReplacementPattern)
            codomain (.subst body leftReplacement))
          (.mk available outer (.subst bodyPattern rightReplacementPattern)
            codomain (.subst body rightReplacement))
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {leftPatterns rightPatterns : List Pattern}
        {rest : Option String} {elementType : TypeExpr}
        {leftElements rightElements : List (CostTreeDecoration source)}
        (elements : CostTreeDecorationListTransport source staticLift
          leftElements rightElements) :
        CostTreeDecorationTransport source staticLift
          (.mk available outer (.collection collectionType leftPatterns rest)
            (.collection collectionType elementType)
            (.collection leftElements))
          (.mk available outer (.collection collectionType rightPatterns rest)
            (.collection collectionType elementType)
            (.collection rightElements))

  /-- Positional transport for equation-neutral argument and collection
  frames. Nonlinear duplication/discarding occurs only at explicit static
  boundary maps. -/
  inductive CostTreeDecorationListTransport (source : CIGSLT)
      (staticLift : CostStaticPlanLift source) :
      List (CostTreeDecoration source) →
      List (CostTreeDecoration source) → Prop where
    | nil : CostTreeDecorationListTransport source staticLift [] []
    | cons {leftHead rightHead : CostTreeDecoration source}
        {leftTail rightTail : List (CostTreeDecoration source)}
        (head : CostTreeDecorationTransport source staticLift
          leftHead rightHead)
        (tail : CostTreeDecorationListTransport source staticLift
          leftTail rightTail) :
        CostTreeDecorationListTransport source staticLift
          (leftHead :: leftTail) (rightHead :: rightTail)
end

namespace CostTreeDecorationTransport

/-- Structural decoration transport never changes the generated type or
binder-split fiber. -/
theorem sameFiber {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {first second : CostTreeDecoration source}
    (transport : CostTreeDecorationTransport source staticLift first second) :
    CostTreeDecoration.SameFiber first second := by
  cases transport with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | static planStep children =>
      exact
        { available_eq := (staticLift.preservesFiber planStep).targetBound_eq
          outer_eq := rfl
          type_eq := rfl }
  | neutralApplication arguments => exact ⟨rfl, rfl, rfl⟩
  | lambda body => exact ⟨rfl, rfl, rfl⟩
  | multiLambda body => exact ⟨rfl, rfl, rfl⟩
  | substBody body => exact ⟨rfl, rfl, rfl⟩
  | substReplacement replacement => exact ⟨rfl, rfl, rfl⟩
  | collection elements => exact ⟨rfl, rfl, rfl⟩

/-- Structural transport cannot change the outer elaboration constructor,
static colour/source sort, or neutral declaration identity. -/
theorem rootIdentity_eq {source : CIGSLT}
    {staticLift : CostStaticPlanLift source}
    {first second : CostTreeDecoration source}
    (transport : CostTreeDecorationTransport source staticLift first second) :
    first.rootIdentity = second.rootIdentity := by
  cases transport <;> rfl

end CostTreeDecorationTransport

mutual
  /-- Erasing actual typed-tree transport yields the corresponding transport
  of nondependent decoration snapshots.  The converse is intentionally
  absent: a snapshot does not contain enough evidence to reconstruct a typed
  semantic edge. -/
  theorem CostRegionTreeTransport.toDecoration
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      {targetFree : WellSorted.FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (transport : CostRegionTreeTransport source staticLift targetFree left
        right) :
      CostTreeDecorationTransport source staticLift left.decoration
        right.decoration :=
    match transport with
    | .refl tree => .refl tree.decoration
    | .static leftNode rightNode leftChildren rightChildren sourceSortEq
        planStep children => by
        have erasedChildren : ∀ targetIndex,
            CostTreeDecorationTransport source staticLift
              (leftChildren.decorations.get
                ((staticLift.boundaryMap planStep).pullback targetIndex)).2
              (rightChildren.decorations.get targetIndex).2 := by
          intro targetIndex
          have childStep := (children targetIndex).toDecoration
          have leftProjection :
              (leftChildren.getDecoration
                  ((staticLift.boundaryMap planStep).pullback targetIndex)).tree.decoration =
                (leftChildren.decorations.get
                  ((staticLift.boundaryMap planStep).pullback targetIndex)).2 := by
            simpa only [CostRegionBoundaryTreeEntry.decoration] using
              congrArg Prod.snd
                (leftChildren.getDecoration_decoration
                  ((staticLift.boundaryMap planStep).pullback targetIndex))
          have rightProjection :
              (rightChildren.getDecoration targetIndex).tree.decoration =
                (rightChildren.decorations.get targetIndex).2 := by
            simpa only [CostRegionBoundaryTreeEntry.decoration] using
              congrArg Prod.snd
                (rightChildren.getDecoration_decoration targetIndex)
          rw [leftProjection, rightProjection] at childStep
          exact childStep
        have sourceNameEq : leftNode.sourceSort.1 = rightNode.sourceSort.1 :=
          congrArg Subtype.val sourceSortEq
        simpa only [CostRegionTree.decoration,
          CostStaticRegionPlan.decoration_targetBound,
          CostStaticRegionPlan.decoration_pattern,
          CostStaticColor.mapLangSort_name, sourceNameEq] using
          CostTreeDecorationTransport.static
            (type := .base
              (CostStaticColor.mapLangSort source _ leftNode.sourceSort).1)
            (sourceSort := leftNode.sourceSort.1)
            planStep erasedChildren
    | .neutralApplicationOrdinary _ _ constructor _ _ _ _ _ arguments =>
        .neutralApplication arguments.toDecorationList
    | .neutralApplicationQuote _ _ constructor _ _ _ _ _ arguments =>
        .neutralApplication arguments.toDecorationList
    | .lambda _ _ body => .lambda body.toDecoration
    | .multiLambda _ _ body => .multiLambda body.toDecoration
    | .substBody _ _ replacementTree body =>
        .substBody (domain := replacementTree.decoration.type)
          body.toDecoration
    | .substReplacement _ leftTree _ replacement =>
        .substReplacement (domain := leftTree.decoration.type)
          replacement.toDecoration
    | .collection _ _ elements => .collection elements.toDecorationList

  /-- Positional argument transport erases pointwise to positional decoration
  transport. -/
  theorem CostRegionArgumentTreesTransport.toDecorationList
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (transport : CostRegionArgumentTreesTransport source staticLift
        targetFree left right) :
      CostTreeDecorationListTransport source staticLift left.decorations
        right.decorations :=
    match transport with
    | .nil => .nil
    | .cons _ _ _ _ _ _ _ head tail =>
        .cons head.toDecoration tail.toDecorationList

  /-- Homogeneous-element transport erases pointwise to positional decoration
  transport. -/
  theorem CostRegionElementTreesTransport.toDecorationList
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (transport : CostRegionElementTreesTransport source staticLift targetFree
        left right) :
      CostTreeDecorationListTransport source staticLift left.decorations
        right.decorations :=
    match transport with
    | .nil _ _ _ => .nil
    | .cons _ _ _ _ head tail =>
        .cons head.toDecoration tail.toDecorationList
end

namespace CostRegionTreeTransport

/-- Semantic content of one proof-relevant tree transport in its exact split
binder fiber.

The relation is stated in the left endpoint's fiber.  The right endpoint is
transported only along the equalities derived from the typed structural edge;
its raw pattern and all admission evidence are unchanged. -/
def FiberEquation
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter leftPattern
      leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (transport : CostRegionTreeTransport source staticLift targetFree left
      right) : Prop :=
  ∀ (leftCanonical : leftPattern.hasCanonicalBinderMetadata = true)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (leftScope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      leftAvailable.length leftPattern)
    (rightCanonical : rightPattern.hasCanonicalBinderMetadata = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (rightScope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      rightAvailable.length rightPattern),
    let fiber := transport.sameFiber
    (WellSorted.AvailableOpenPattern.equationSetoid
      source.costWholeLanguage targetFree leftAvailable leftOuter leftType).r
      (left.originalAvailableOpenPattern leftCanonical leftObject leftScope)
      ((right.originalAvailableOpenPattern rightCanonical rightObject
        rightScope).reindexFiber fiber.1.symm fiber.2.1.symm
          fiber.2.2.symm)

/-- Reflexive typed transport carries the reflexive authored equation path. -/
theorem refl_fiberEquation
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    FiberEquation
      (CostRegionTreeTransport.refl (staticLift := staticLift) tree) := by
  intro leftCanonical leftObject leftScope rightCanonical rightObject
    rightScope
  have endpoints :
      tree.originalAvailableOpenPattern leftCanonical leftObject leftScope =
        (tree.originalAvailableOpenPattern rightCanonical rightObject
          rightScope).reindexFiber rfl rfl rfl := by
    apply WellSorted.AvailableOpenPattern.ext
    rfl
  rw [endpoints]
  exact Relation.EqvGen.refl _

end CostRegionTreeTransport

namespace CIGSLT

/-- The one genuinely semantic kernel required for structural Cost
transport.

The premise supplies authored equation paths for every recursively selected
boundary child.  The conclusion must transport the exact mapped source
occurrence through binder thinning and the finite boundary pullback.  All
neutral frames are excluded from this law and are discharged generically by
typed contextual congruence below. -/
def CostStaticRegionTransportSound (source : CIGSLT)
    (staticLift : CostStaticPlanLift source) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {outer : List TypeExpr}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    (leftChildren : CostRegionBoundaryTrees source targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees source targetFree color
      rightNode.finiteBoundaryTable)
    (sourceSortEq : leftNode.sourceSort = rightNode.sourceSort)
    (planStep : staticLift.Edge leftNode.plan.decoration
      rightNode.plan.decoration leftChildren.decorations
        rightChildren.decorations)
    (children : ∀ targetIndex,
      CostRegionTreeTransport source staticLift targetFree
        (leftChildren.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightChildren.getDecoration targetIndex).tree),
    (∀ targetIndex, (children targetIndex).FiberEquation) →
      (CostRegionTreeTransport.static (outer := outer) leftNode rightNode
        leftChildren rightChildren sourceSortEq planStep children
        ).FiberEquation

/-- Support-erasure theorem required of the concrete typed tree transport.

The structural relation itself retains the exact source occurrence.  This
law proves that, after static mapping, binder thinning, supported boundary
restoration, and recursive contextual lifting, one structural edge erases to
an authored Cost equation path.  A path rather than a single generator is
essential: supported substitution can refine one source occurrence into
several target generators. -/
def CostStructuralTransportSound (source : CIGSLT)
    (staticLift : CostStaticPlanLift source) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort},
    CostRegionTreeTransport source staticLift targetFree
        left.2.tree right.2.tree →
      (openEquationSetoid source.costIGSLT targetFree targetBound
        targetSort).r (CostOpenElaboration.erase left)
          (CostOpenElaboration.erase right)

/-- A concrete Cost elaboration path lift.  Its elementary evidence is only
the recursive proof-relevant transport; semantic support is the separately
proved erasure theorem, never an independently chosen target generator. -/
def costStructuralPathLift (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift) :
    OpenElaborationPathLift source.costOpenElaborationCarrier where
  step := fun _targetFree _targetBound _targetSort left right =>
    CostRegionTreeTransport source staticLift _targetFree
      left.2.tree right.2.tree
  erasesToAuthoredPath := fun transport => sound transport

/-- The least proof-relevant Cost equation semantics generated by one lawful
static-plan lift and the recursive neutral-frame transport. -/
def costStructuralSemantics (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift) :
    OpenElaborationSemantics source.costOpenElaborationCarrier :=
  OpenElaborationSemantics.ofPathLift
    (source.costStructuralPathLift staticLift sound)

/-- Structural Cost equivalence is always sound for compact authored
observation.  The converse is deliberately absent because erasure forgets
colour, declaration, and occurrence identity. -/
theorem costStructuralSemantics_implies_compactObservation (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (equivalent :
      (source.costStructuralSemantics staticLift sound).relation
        targetFree targetBound targetSort left right) :
    (source.costOpenElaborationCarrier.compactObservationSetoid
      targetFree targetBound targetSort).r left right :=
  (source.costStructuralSemantics staticLift sound).erasesToAuthored equivalent

/-- Every path in structural Cost semantics retains its root identity.  In
particular, compactly overlapping base and wrapped roots remain distinct. -/
theorem costStructuralSemantics_rootIdentity_eq (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (equivalent :
      (source.costStructuralSemantics staticLift sound).relation
        targetFree targetBound targetSort left right) :
    left.decoration.rootIdentity = right.decoration.rootIdentity := by
  change Relation.EqvGen
    ((source.costStructuralPathLift staticLift sound).step
      targetFree targetBound targetSort) left right at equivalent
  induction equivalent with
  | rel left right transport => exact transport.rootIdentity_eq
  | refl term => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- A root-identity mismatch is a constructive obstruction to structural
Cost equivalence, even if compact syntax has forgotten the mismatch. -/
theorem not_costStructuralSemantics_of_rootIdentity_ne (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    ¬ (source.costStructuralSemantics staticLift sound).relation
        targetFree targetBound targetSort left right := by
  intro equivalent
  exact different
    (source.costStructuralSemantics_rootIdentity_eq staticLift sound equivalent)

/-- Same compact syntax but different retained root identity is the concrete
positive/negative boundary: compact observation relates the pair, while the
proof-relevant Cost semantics rejects it. -/
theorem compact_but_not_costStructuralSemantics (source : CIGSLT)
    (staticLift : CostStaticPlanLift source)
    (sound : source.CostStructuralTransportSound staticLift)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right)
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    (source.costOpenElaborationCarrier.compactObservationSetoid
        targetFree targetBound targetSort).r left right ∧
      ¬ (source.costStructuralSemantics staticLift sound).relation
        targetFree targetBound targetSort left right :=
  ⟨source.costOpenElaborationCarrier.compactObservation_of_erase_eq
      sameErasure,
    source.not_costStructuralSemantics_of_rootIdentity_ne staticLift sound
      different⟩

end CIGSLT

end Mettapedia.GSLT.LanguageDef
