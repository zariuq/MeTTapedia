import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAvailabilityTransposition
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms

/-!
# Whole-tree availability transposition for hereditary rho normalization

The static-node theorem has already discharged the semantic interaction
between planner support, keyed canonicalization, and endpoint restoration.
This module lifts that result through the alternating region tree.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

/-- A certified static root is never a bound-variable leaf. -/
private theorem term_ne_bvar {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree) (index : Nat) :
    node.term.1 ≠ .bvar index := by
  intro equality
  rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩ <;>
    rw [equality] at shape <;> cases shape

/-- A certified static root is never a free-variable leaf. -/
private theorem term_ne_fvar {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree) (name : String) :
    node.term.1 ≠ .fvar name := by
  intro equality
  rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩ <;>
    rw [equality] at shape <;> cases shape

/-- A certified static root is never a lambda frame. -/
private theorem term_ne_lambda {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (binder : Option String) (body : Pattern) :
    node.term.1 ≠ .lambda binder body := by
  intro equality
  rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩ <;>
    rw [equality] at shape <;> cases shape

/-- A certified static root is never a multi-lambda frame. -/
private theorem term_ne_multiLambda {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (arity : Nat) (binders : List String) (body : Pattern) :
    node.term.1 ≠ .multiLambda arity binders body := by
  intro equality
  rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩ <;>
    rw [equality] at shape <;> cases shape

/-- A certified static root is never explicit substitution syntax. -/
private theorem term_ne_subst {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (body replacement : Pattern) :
    node.term.1 ≠ .subst body replacement := by
  intro equality
  rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩ <;>
    rw [equality] at shape <;> cases shape

/-- Equal rendered labels decode to the same declared constructor. -/
private theorem declaredConstructor_eq_of_materialized_label_eq
    (first second : rhoCIGSLT.DeclaredCostConstructor)
    (labelEq : (rhoCIGSLT.materializeDeclaredCostConstructor first).label =
      (rhoCIGSLT.materializeDeclaredCostConstructor second).label) :
    first = second := by
  have firstDecoded : rhoCIGSLT.decodeDeclaredCostConstructor
      (rhoCIGSLT.materializeDeclaredCostConstructor first).label = some first := by
    rw [rhoCIGSLT.materializeDeclaredCostConstructor_label first]
    exact rhoCIGSLT.decodeDeclaredCostConstructor_render first
  have secondDecoded : rhoCIGSLT.decodeDeclaredCostConstructor
      (rhoCIGSLT.materializeDeclaredCostConstructor second).label = some second := by
    rw [rhoCIGSLT.materializeDeclaredCostConstructor_label second]
    exact rhoCIGSLT.decodeDeclaredCostConstructor_render second
  exact Option.some.inj
    (firstDecoded.symm.trans ((congrArg
      rhoCIGSLT.decodeDeclaredCostConstructor labelEq).trans secondDecoded))

/-- For rho, a raw static root and its generated result fibre determine the
static colour even when the active binder contexts differ. -/
private theorem static_color_eq_of_term_and_type
    {firstColor secondColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (first : CostStaticRegionNode rhoCIGSLT firstColor targetFree)
    (second : CostStaticRegionNode rhoCIGSLT secondColor targetFree)
    (termEq : first.term.1 = second.term.1)
    (typeEq : TypeExpr.base
        (firstColor.mapLangSort rhoCIGSLT first.sourceSort).1 =
      TypeExpr.base
        (secondColor.mapLangSort rhoCIGSLT second.sourceSort).1) :
    firstColor = secondColor := by
  rcases first.plan.pattern_shape_of_isStaticRoot first.rootStatic with
      ⟨wireName, arguments, shape⟩ |
      ⟨collectionType, elements, rest, shape⟩
  · obtain ⟨firstConstructor, firstDecoded, firstRole⟩ :=
      first.plan.application_dispatch_of_isStaticRoot first.rootStatic shape
    obtain ⟨secondConstructor, secondDecoded, secondRole⟩ :=
      second.plan.application_dispatch_of_isStaticRoot second.rootStatic
        (termEq.symm.trans shape)
    have constructorEq : firstConstructor = secondConstructor :=
      Option.some.inj (firstDecoded.symm.trans secondDecoded)
    subst secondConstructor
    exact CIGSLT.GeneratedCostConstructorRole.static.inj
      (firstRole.symm.trans secondRole)
  · have firstInteracting :=
      CostCanonicalLaws.rho_collection_node_sourceSort_interacting first shape
    have secondInteracting :=
      CostCanonicalLaws.rho_collection_node_sourceSort_interacting second
        (termEq.symm.trans shape)
    have mappedEq : firstColor.mapLangSort rhoCIGSLT first.sourceSort =
        secondColor.mapLangSort rhoCIGSLT second.sourceSort := by
      apply Subtype.ext
      exact TypeExpr.base.inj typeEq
    exact CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting rhoCIGSLT
      firstColor secondColor first.sourceSort second.sourceSort
        firstInteracting secondInteracting mappedEq

/-- Once the colour is fixed, equality of generated result fibres reflects
to equality of the authored source sorts. -/
private theorem static_sourceSort_eq_of_type
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (first second : CostStaticRegionNode rhoCIGSLT color targetFree)
    (typeEq : TypeExpr.base
        (color.mapLangSort rhoCIGSLT first.sourceSort).1 =
      TypeExpr.base
        (color.mapLangSort rhoCIGSLT second.sourceSort).1) :
    first.sourceSort = second.sourceSort := by
  apply CostStaticColor.mapLangSort_injective rhoCIGSLT color
  apply Subtype.ext
  exact TypeExpr.base.inj typeEq

/-- Positional selection from a finite boundary forest strictly decreases
the alternating-tree weight. -/
private theorem boundary_getDecoration_weight_lt
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree occurrences}
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color table)
    (position : Fin trees.decorations.length) :
    (trees.getDecoration position).tree.weight < trees.weight :=
  match trees, position with
  | .nil, position => Fin.elim0 position
  | .cons head tail, ⟨0, _⟩ => by
      change head.weight < head.weight + tail.weight + 1
      omega
  | .cons head tail, ⟨position + 1, inBounds⟩ => by
      have smaller := boundary_getDecoration_weight_lt tail
        ⟨position, Nat.lt_of_succ_lt_succ inBounds⟩
      change (tail.getDecoration
        ⟨position, Nat.lt_of_succ_lt_succ inBounds⟩).tree.weight <
          head.weight + tail.weight + 1
      omega
  termination_by trees.weight
  decreasing_by
    simp [CostRegionBoundaryTrees.weight]
    omega

private theorem boundary_getEntry_weight_lt
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree occurrences}
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color table)
    (position : Fin table.entries.length) :
    (trees.getEntry position).tree.weight < trees.weight :=
  boundary_getDecoration_weight_lt trees
    (Fin.cast (trees.decorations_length_eq_entries_length).symm position)

/-- In one exact binder fibre, structural unambiguity identifies normalized
argument spines without identifying proof-relevant decomposition trees. -/
private theorem argument_normalize_eq_of_unambiguous
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (first second : CostRegionArgumentTrees rhoCIGSLT targetFree available outer
      arguments parameters)
    (objects : WellSorted.isObjectPatternList arguments = true) :
    (first.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns =
    (second.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns :=
  match first, second with
  | .nil, .nil => rfl
  | @CostRegionArgumentTrees.cons _ _ _ _ argument arguments parameter
        parameters expected firstRepresentation firstParameterType firstHead
        firstTail,
      @CostRegionArgumentTrees.cons _ _ _ _ _ _ _ _ secondExpected secondRepresentation
        secondParameterType secondHead secondTail => by
        have expectedEq : expected = secondExpected := Option.some.inj
          (firstParameterType.symm.trans secondParameterType)
        subst_vars
        have objectParts : WellSorted.isObjectPattern argument = true ∧
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPatternList] using objects
        simp only [CostRegionArgumentTrees.normalize]
        exact congrArg₂ List.cons
          (CostRegionTree.normalize_pattern_eq_of_unambiguous
            CostCanonicalLaws.rho_unambiguousStaticDecomposition
            rhoHereditaryNormalizationKernel firstHead secondHead
              objectParts.1)
          (argument_normalize_eq_of_unambiguous firstTail secondTail
            objectParts.2)
  termination_by first.weight
  decreasing_by
    simp [CostRegionArgumentTrees.weight]
    omega

set_option maxRecDepth 5000
set_option maxHeartbeats 300000

mutual
  /-- Hereditary rho normalization is invariant when an ambient binder suffix
  is moved into the active availability of an object tree.  The two trees may
  retain different proof-relevant decompositions; only their raw pattern and
  result type are identified. -/
  theorem CostRegionTree.normalize_pattern_eq_of_availableSuffix
      {targetFree : WellSorted.FreeTypeContext}
      {smallAvailable largeAvailable ambient : List TypeExpr}
      {smallPattern largePattern : Pattern}
      {smallType largeType : TypeExpr}
      (availableSuffix : largeAvailable = smallAvailable ++ ambient)
      (small : CostRegionTree rhoCIGSLT targetFree smallAvailable []
        smallPattern smallType)
      (large : CostRegionTree rhoCIGSLT targetFree largeAvailable []
        largePattern largeType)
      (patternEq : smallPattern = largePattern)
      (typeEq : smallType = largeType)
      (object : WellSorted.isObjectPattern smallPattern = true) :
      (small.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (large.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    match small with
    | @CostRegionTree.bvar _ _ _ _ index _ smallLookup => by
        cases large with
        | bvar largeLookup =>
            cases patternEq
            simp [CostRegionTree.normalize]
        | fvar largeLookup => cases patternEq
        | static node children =>
            exact (term_ne_bvar node index patternEq.symm).elim
        | neutralApplicationOrdinary => cases patternEq
        | neutralApplicationQuote => cases patternEq
        | lambda => cases patternEq
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.fvar _ _ _ _ name _ smallLookup => by
        cases large with
        | bvar largeLookup => cases patternEq
        | fvar largeLookup =>
            cases patternEq
            simp [CostRegionTree.normalize]
        | static node children =>
            exact (term_ne_fvar node name patternEq.symm).elim
        | neutralApplicationOrdinary => cases patternEq
        | neutralApplicationQuote => cases patternEq
        | lambda => cases patternEq
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.static _ _ smallColor _ smallNode smallTrees => by
        cases large with
        | bvar largeLookup =>
            exact (term_ne_bvar smallNode _ patternEq).elim
        | fvar largeLookup =>
            exact (term_ne_fvar smallNode _ patternEq).elim
        | @static largeColor _ largeNode largeTrees =>
            have colorEq := static_color_eq_of_term_and_type smallNode largeNode
              patternEq typeEq
            cases colorEq
            have sourceSortEq := static_sourceSort_eq_of_type smallNode
              largeNode typeEq
            have sourceTypeEq : TypeExpr.base smallNode.sourceSort.1 =
                TypeExpr.base largeNode.sourceSort.1 :=
              congrArg (fun sort => TypeExpr.base sort.1) sourceSortEq
            obtain ⟨occurrencesEq, tables, _abstractAligned⟩ :=
              CostStaticRegionPlan.boundaryTablesAndAbstractAvailabilitySuffix_of_scoped
                CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
                (show CostStaticAvailabilityAt ambient .exposed
                    smallNode.targetBound largeNode.targetBound from
                  availableSuffix)
                availableSuffix patternEq sourceTypeEq object
                  smallNode.term.2.1.isWellScopedAt smallNode.plan largeNode.plan
            have childNormalEq : ∀
                (smallPosition : Fin smallNode.boundaryTable.entries.length)
                (largePosition : Fin largeNode.boundaryTable.entries.length),
                smallPosition.1 = largePosition.1 →
                ((smallTrees.getEntry smallPosition).tree.normalize
                    (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
                  ((largeTrees.getEntry largePosition).tree.normalize
                    (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
              intro smallPosition largePosition positionEq
              let castPosition : Fin
                  (TypedCostRegionBoundaryTable.cast occurrencesEq
                    smallNode.boundaryTable).entries.length :=
                Fin.cast (by simp) smallPosition
              let alignedPosition : Fin largeNode.boundaryTable.entries.length :=
                Fin.cast
                  (TypedCostRegionBoundaryTable.AvailabilitySuffix.entries_length_eq
                    tables) castPosition
              have alignedPositionEq : alignedPosition = largePosition := by
                apply Fin.ext
                simpa [alignedPosition, castPosition] using positionEq
              have selected :=
                TypedCostRegionBoundaryTable.AvailabilitySuffix.getEntry
                  tables castPosition
              have selected' : TypedCostRegionBoundary.AvailabilitySuffix ambient
                  (smallNode.boundaryTable.entries.get smallPosition)
                  (largeNode.boundaryTable.entries.get largePosition) := by
                rw [← alignedPositionEq]
                simpa [CostStaticRegionNode.boundaryTable, castPosition,
                  alignedPosition] using selected
              have smallBoundaryEq :=
                smallTrees.getEntry_boundary smallPosition
              have largeBoundaryEq :=
                largeTrees.getEntry_boundary largePosition
              have childPatternEq :
                  (smallTrees.getEntry smallPosition).boundary.boundary.content =
                    (largeTrees.getEntry largePosition).boundary.boundary.content := by
                rw [smallBoundaryEq, largeBoundaryEq]
                exact selected'.content_eq
              have childTypeEq :
                  (smallTrees.getEntry smallPosition).boundary.boundary.targetType =
                    (largeTrees.getEntry largePosition).boundary.boundary.targetType := by
                rw [smallBoundaryEq, largeBoundaryEq]
                exact selected'.targetType_eq
              have childSuffix : CostStaticAvailabilitySuffix ambient
                  (smallTrees.getEntry smallPosition).boundary.boundary.targetSupport
                  (largeTrees.getEntry largePosition).boundary.boundary.targetSupport := by
                rw [smallBoundaryEq, largeBoundaryEq]
                exact selected'.targetSupport
              have childWeight := boundary_getEntry_weight_lt smallTrees
                smallPosition
              rcases childSuffix with exposed | sealed
              · exact CostRegionTree.normalize_pattern_eq_of_availableSuffix
                  exposed (smallTrees.getEntry smallPosition).tree
                    (largeTrees.getEntry largePosition).tree childPatternEq
                      childTypeEq
                        (smallTrees.getEntry smallPosition).boundary.contentObjectPattern
              · exact CostRegionTree.normalize_pattern_eq_of_availableSuffix
                  (ambient := []) (by simpa using sealed)
                    (smallTrees.getEntry smallPosition).tree
                      (largeTrees.getEntry largePosition).tree childPatternEq
                        childTypeEq
                          (smallTrees.getEntry smallPosition).boundary.contentObjectPattern
            rw [CostRegionTree.normalize_static_pattern,
              CostRegionTree.normalize_static_pattern]
            convert
              normalizeHereditary_static_eq_of_availabilitySuffix smallNode
                largeNode smallTrees largeTrees availableSuffix sourceSortEq
                  patternEq childNormalEq using 1 <;> rfl
        | neutralApplicationOrdinary _ _ constructor materializes neutral _ _ =>
            exact (smallNode.not_neutralApplication patternEq constructor
              materializes neutral).elim
        | neutralApplicationQuote _ _ constructor materializes neutral _ _ =>
            exact (smallNode.not_neutralApplication patternEq constructor
              materializes neutral).elim
        | lambda => exact (term_ne_lambda smallNode _ _ patternEq).elim
        | multiLambda =>
            exact (term_ne_multiLambda smallNode _ _ _ patternEq).elim
        | subst => exact (term_ne_subst smallNode _ _ patternEq).elim
        | collection => cases typeEq
    | @CostRegionTree.neutralApplicationOrdinary _ _ _ _ smallRule
        smallArguments smallMembership smallNotBare smallConstructor
        smallMaterializes smallNeutral smallOrdinary smallChildren => by
        cases large with
        | bvar => cases patternEq
        | fvar => cases patternEq
        | static largeNode largeTrees =>
            exact (largeNode.not_neutralApplication patternEq.symm
              smallConstructor smallMaterializes smallNeutral).elim
        | @neutralApplicationOrdinary _ _ largeRule largeArguments
            largeMembership largeNotBare largeConstructor largeMaterializes
            largeNeutral largeOrdinary largeChildren =>
            obtain ⟨labelEq, argumentsEq⟩ := Pattern.apply.inj patternEq
            have constructorEq := declaredConstructor_eq_of_materialized_label_eq
              smallConstructor largeConstructor (by
                rw [smallMaterializes, largeMaterializes]
                exact labelEq)
            cases constructorEq
            have ruleEq : smallRule = largeRule :=
              smallMaterializes.symm.trans largeMaterializes
            cases ruleEq
            cases argumentsEq
            have argumentObjects :
                WellSorted.isObjectPatternList smallArguments = true := by
              simpa [WellSorted.isObjectPattern] using object
            simpa only [CostRegionTree.normalize] using congrArg
              (Pattern.apply smallRule.label)
              (CostRegionArgumentTrees.normalize_patterns_eq_of_availableSuffix
                availableSuffix smallChildren largeChildren argumentObjects)
        | @neutralApplicationQuote _ _ largeRule largeArguments
            largeMembership largeNotBare largeConstructor largeMaterializes
            largeNeutral largeQuoted largeChildren =>
            obtain ⟨labelEq, argumentsEq⟩ := Pattern.apply.inj patternEq
            have constructorEq := declaredConstructor_eq_of_materialized_label_eq
              smallConstructor largeConstructor (by
                rw [smallMaterializes, largeMaterializes]
                exact labelEq)
            cases constructorEq
            have ruleEq : smallRule = largeRule :=
              smallMaterializes.symm.trans largeMaterializes
            cases ruleEq
            rw [largeQuoted] at smallOrdinary
            contradiction
        | lambda => cases patternEq
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.neutralApplicationQuote _ _ smallAvailable _ smallRule
        smallArguments smallMembership smallNotBare smallConstructor
        smallMaterializes smallNeutral smallQuoted smallChildren => by
        cases large with
        | bvar => cases patternEq
        | fvar => cases patternEq
        | static largeNode largeTrees =>
            exact (largeNode.not_neutralApplication patternEq.symm
              smallConstructor smallMaterializes smallNeutral).elim
        | @neutralApplicationOrdinary _ _ largeRule largeArguments
            largeMembership largeNotBare largeConstructor largeMaterializes
            largeNeutral largeOrdinary largeChildren =>
            obtain ⟨labelEq, argumentsEq⟩ := Pattern.apply.inj patternEq
            have constructorEq := declaredConstructor_eq_of_materialized_label_eq
              smallConstructor largeConstructor (by
                rw [smallMaterializes, largeMaterializes]
                exact labelEq)
            cases constructorEq
            have ruleEq : smallRule = largeRule :=
              smallMaterializes.symm.trans largeMaterializes
            cases ruleEq
            rw [smallQuoted] at largeOrdinary
            contradiction
        | @neutralApplicationQuote largeAvailable _ largeRule
            largeArguments largeMembership largeNotBare largeConstructor
            largeMaterializes largeNeutral largeQuoted largeChildren =>
            obtain ⟨labelEq, argumentsEq⟩ := Pattern.apply.inj patternEq
            have constructorEq := declaredConstructor_eq_of_materialized_label_eq
              smallConstructor largeConstructor (by
                rw [smallMaterializes, largeMaterializes]
                exact labelEq)
            cases constructorEq
            have ruleEq : smallRule = largeRule :=
              smallMaterializes.symm.trans largeMaterializes
            cases ruleEq
            cases argumentsEq
            subst largeAvailable
            have argumentObjects :
                WellSorted.isObjectPatternList smallArguments = true := by
              simpa [WellSorted.isObjectPattern] using object
            let smallExtended : CostRegionArgumentTrees rhoCIGSLT targetFree []
                (smallAvailable ++ ambient ++ []) smallArguments
                  smallRule.params :=
              (smallChildren.extendOuter ambient).reindexOuter (by simp)
            let largeReindexed : CostRegionArgumentTrees rhoCIGSLT targetFree []
                (smallAvailable ++ ambient ++ []) smallArguments
                  smallRule.params :=
              largeChildren.reindexOuter (by simp)
            have aligned := argument_normalize_eq_of_unambiguous smallExtended
              largeReindexed argumentObjects
            simpa only [CostRegionTree.normalize] using congrArg
              (Pattern.apply smallRule.label) (by
                simpa [smallExtended, largeReindexed] using aligned)
        | lambda => cases patternEq
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.lambda _ _ _ _ smallBinder smallBody smallDomain
        smallCodomain smallBodyTree => by
        cases large with
        | bvar => cases patternEq
        | fvar => cases patternEq
        | static node children =>
            exact (term_ne_lambda node smallBinder smallBody
              patternEq.symm).elim
        | neutralApplicationOrdinary => cases patternEq
        | neutralApplicationQuote => cases patternEq
        | @lambda _ _ largeBinder largeBody largeDomain largeCodomain
            largeBodyTree =>
            obtain ⟨binderEq, bodyEq⟩ := Pattern.lambda.inj patternEq
            obtain ⟨domainEq, codomainEq⟩ := TypeExpr.arrow.inj typeEq
            cases binderEq
            cases bodyEq
            cases domainEq
            cases codomainEq
            have bodyObject : WellSorted.isObjectPattern smallBody = true := by
              simpa [WellSorted.isObjectPattern] using object
            have bodySuffix : smallDomain :: largeAvailable =
                (smallDomain :: smallAvailable) ++ ambient := by
              simpa only [List.cons_append] using
                congrArg (smallDomain :: ·) availableSuffix
            simpa only [CostRegionTree.normalize] using congrArg
              (Pattern.lambda smallBinder)
              (CostRegionTree.normalize_pattern_eq_of_availableSuffix
                bodySuffix smallBodyTree largeBodyTree rfl rfl bodyObject)
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.multiLambda _ _ _ _ smallArity smallBinders smallBody
        smallDomain smallCodomain smallBodyTree => by
        cases large with
        | bvar => cases patternEq
        | fvar => cases patternEq
        | static node children =>
            exact (term_ne_multiLambda node smallArity smallBinders smallBody
              patternEq.symm).elim
        | neutralApplicationOrdinary => cases patternEq
        | neutralApplicationQuote => cases patternEq
        | lambda => cases patternEq
        | @multiLambda _ _ largeArity largeBinders largeBody largeDomain
            largeCodomain largeBodyTree =>
            obtain ⟨arityEq, bindersEq, bodyEq⟩ :=
              Pattern.multiLambda.inj patternEq
            obtain ⟨domainEq, codomainEq⟩ := TypeExpr.arrow.inj typeEq
            cases arityEq
            cases bindersEq
            cases bodyEq
            cases domainEq
            cases codomainEq
            have bodyObject : WellSorted.isObjectPattern smallBody = true := by
              simpa [WellSorted.isObjectPattern] using object
            have bodySuffix :
                List.replicate smallArity smallDomain ++ largeAvailable =
                  (List.replicate smallArity smallDomain ++ smallAvailable) ++
                    ambient := by
              simpa only [List.append_assoc] using congrArg
                (List.replicate smallArity smallDomain ++ ·) availableSuffix
            simpa only [CostRegionTree.normalize] using congrArg
              (Pattern.multiLambda smallArity smallBinders)
              (CostRegionTree.normalize_pattern_eq_of_availableSuffix
                bodySuffix smallBodyTree largeBodyTree rfl rfl bodyObject)
        | subst => cases patternEq
        | collection => cases patternEq
    | @CostRegionTree.subst _ _ _ _ body replacement _ _ bodyTree
        replacementTree => by
        simp [WellSorted.isObjectPattern] at object
    | @CostRegionTree.collection _ _ _ _ smallCollectionType smallElements
        smallRest smallElementType smallChildren => by
        cases large with
        | bvar => cases patternEq
        | fvar => cases patternEq
        | static => cases typeEq
        | neutralApplicationOrdinary => cases patternEq
        | neutralApplicationQuote => cases patternEq
        | lambda => cases patternEq
        | multiLambda => cases patternEq
        | subst => cases patternEq
        | @collection _ _ largeCollectionType largeElements largeRest
            largeElementType largeChildren =>
            obtain ⟨collectionTypeEq, elementsEq, restEq⟩ :=
              Pattern.collection.inj patternEq
            have elementTypeEq : smallElementType = largeElementType := by
              injection typeEq
            cases collectionTypeEq
            cases elementsEq
            cases restEq
            cases elementTypeEq
            have objectParts : smallRest.isNone = true ∧
                WellSorted.isObjectPatternList smallElements = true := by
              simpa [WellSorted.isObjectPattern] using object
            have elementObjects :
                WellSorted.isObjectPatternList smallElements = true :=
              objectParts.2
            simpa only [CostRegionTree.normalize] using congrArg
              (fun elements => Pattern.collection smallCollectionType elements
                smallRest)
              (CostRegionElementTrees.normalize_patterns_eq_of_availableSuffix
                availableSuffix smallChildren largeChildren elementObjects)
    termination_by small.weight
    decreasing_by
      all_goals simp [CostRegionTree.weight]
      all_goals omega

  /-- The tree theorem lifts pointwise through an authored constructor spine. -/
  theorem CostRegionArgumentTrees.normalize_patterns_eq_of_availableSuffix
      {targetFree : WellSorted.FreeTypeContext}
      {smallAvailable largeAvailable ambient : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (availableSuffix : largeAvailable = smallAvailable ++ ambient)
      (small : CostRegionArgumentTrees rhoCIGSLT targetFree smallAvailable []
        arguments parameters)
      (large : CostRegionArgumentTrees rhoCIGSLT targetFree largeAvailable []
        arguments parameters)
      (objects : WellSorted.isObjectPatternList arguments = true) :
      (small.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns =
      (large.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns :=
    match small, large with
    | .nil, .nil => by
        simp [CostRegionArgumentTrees.normalize]
    | @CostRegionArgumentTrees.cons _ _ _ _ argument arguments parameter
        parameters expected smallRepresentation smallParameterType smallHead
        smallTail,
      @CostRegionArgumentTrees.cons _ _ _ _ _ _ _ _ largeExpected
        largeRepresentation largeParameterType largeHead largeTail => by
          have expectedEq : expected = largeExpected := Option.some.inj
            (smallParameterType.symm.trans largeParameterType)
          cases expectedEq
          have objectParts : WellSorted.isObjectPattern argument = true ∧
              WellSorted.isObjectPatternList arguments = true := by
            simpa [WellSorted.isObjectPatternList] using objects
          simp only [CostRegionArgumentTrees.normalize]
          exact congrArg₂ List.cons
            (CostRegionTree.normalize_pattern_eq_of_availableSuffix
              availableSuffix smallHead largeHead rfl rfl objectParts.1)
            (CostRegionArgumentTrees.normalize_patterns_eq_of_availableSuffix
              availableSuffix smallTail largeTail objectParts.2)
    termination_by small.weight
    decreasing_by
      all_goals simp [CostRegionArgumentTrees.weight]
      all_goals omega

  /-- The tree theorem lifts pointwise through a homogeneous collection. -/
  theorem CostRegionElementTrees.normalize_patterns_eq_of_availableSuffix
      {targetFree : WellSorted.FreeTypeContext}
      {smallAvailable largeAvailable ambient : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (availableSuffix : largeAvailable = smallAvailable ++ ambient)
      (small : CostRegionElementTrees rhoCIGSLT targetFree smallAvailable []
        elements elementType)
      (large : CostRegionElementTrees rhoCIGSLT targetFree largeAvailable []
        elements elementType)
      (objects : WellSorted.isObjectPatternList elements = true) :
      (small.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns =
      (large.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns :=
    match small, large with
    | .nil _ _ _, .nil _ _ _ => by
        simp [CostRegionElementTrees.normalize]
    | @CostRegionElementTrees.cons _ _ _ _ element elements elementType
        smallHead smallTail,
      @CostRegionElementTrees.cons _ _ _ _ _ _ _ largeHead largeTail => by
          have objectParts : WellSorted.isObjectPattern element = true ∧
              WellSorted.isObjectPatternList elements = true := by
            simpa [WellSorted.isObjectPatternList] using objects
          simp only [CostRegionElementTrees.normalize]
          exact congrArg₂ List.cons
            (CostRegionTree.normalize_pattern_eq_of_availableSuffix
              availableSuffix smallHead largeHead rfl rfl objectParts.1)
            (CostRegionElementTrees.normalize_patterns_eq_of_availableSuffix
              availableSuffix smallTail largeTail objectParts.2)
    termination_by small.weight
    decreasing_by
      all_goals simp [CostRegionElementTrees.weight]
      all_goals omega
end

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
