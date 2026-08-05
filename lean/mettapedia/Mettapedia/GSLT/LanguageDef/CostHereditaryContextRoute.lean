import Mettapedia.GSLT.LanguageDef.CostGeneratorHereditaryAlignment

/-!
# Single-occurrence routes through hereditary Cost trees

An authored contextual generator changes one syntactic path.  Outside a
static region, that path lifts through ordinary tree constructors while all
siblings remain definitionally unchanged.  At the first static region that
contains the occurrence, routing stops: the complete selected frame is
compared by a semantic-atom root bridge.  In particular, a foreign-colour
boundary is never recursively exposed to the parent canonicalizer.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

namespace CostRegionArgumentTreesNormalizationAlignment

/-- Reflexive alignment of a complete constructor-argument spine. -/
def ofRefl
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters) :
    CostRegionArgumentTreesNormalizationAlignment source kernel targetFree
      trees trees :=
  match trees with
  | .nil => .nil
  | .cons representation parameterType head tail =>
      .cons representation representation parameterType head head tail tail
        (.refl head) (ofRefl tail)

end CostRegionArgumentTreesNormalizationAlignment

namespace CostRegionElementTreesNormalizationAlignment

/-- Reflexive alignment of a complete homogeneous collection spine. -/
def ofRefl
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType) :
    CostRegionElementTreesNormalizationAlignment source kernel targetFree
      trees trees :=
  match trees with
  | .nil _ _ _ => .nil _ _ _
  | .cons head tail =>
      .cons head head tail tail (.refl head) (ofRefl tail)

end CostRegionElementTreesNormalizationAlignment

/-- A one-hole position inside a pattern list.  Keeping the siblings as data
lets argument and collection routes expose their exact active path without
reconstructing it from typing derivations. -/
structure CostPatternListRouteContext where
  before : List Pattern
  inner : OneHoleContext
  after : List Pattern

/-- Recover the compact pattern index of a retained Cost tree. -/
def CostRegionTree.sourcePattern
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (_ : CostRegionTree source targetFree available outer pattern type) : Pattern :=
  pattern

/-- Recover the compact argument-list index of a retained argument spine. -/
def CostRegionArgumentTrees.sourcePatterns
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {parameters : List TermParam}
    (_ : CostRegionArgumentTrees source targetFree available outer patterns
      parameters) : List Pattern :=
  patterns

/-- Recover the compact element-list index of a retained collection spine. -/
def CostRegionElementTrees.sourcePatterns
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {elementType : TypeExpr}
    (_ : CostRegionElementTrees source targetFree available outer patterns
      elementType) : List Pattern :=
  patterns

mutual
  /-- A single root-changing occurrence routed through otherwise identical
  proof-relevant Cost trees.  Static roots have no congruence constructor:
  their complete semantic frame must be discharged by `root`. -/
  inductive CostRegionTreeNormalizationRoute
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {leftAvailable leftOuter : List TypeExpr} →
      {leftPattern : Pattern} → {leftType : TypeExpr} →
      CostRegionTree source targetFree leftAvailable leftOuter leftPattern
          leftType →
      {rightAvailable rightOuter : List TypeExpr} →
      {rightPattern : Pattern} → {rightType : TypeExpr} →
      CostRegionTree source targetFree rightAvailable rightOuter rightPattern
          rightType → Type where
    | root
        {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
        {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
        {left : CostRegionTree source targetFree leftAvailable leftOuter
          leftPattern leftType}
        {right : CostRegionTree source targetFree rightAvailable rightOuter
          rightPattern rightType}
        (bridge : CostRegionRootNormalizationBridge source kernel targetFree
          left right) :
        CostRegionTreeNormalizationRoute source kernel targetFree left right
    | neutralApplicationOrdinary
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ UsesBareCollection rule)
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
        (arguments : CostRegionArgumentTreesNormalizationRoute source kernel
          targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary leftChildren)
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary rightChildren)
    | neutralApplicationQuote
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ UsesBareCollection rule)
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
        (arguments : CostRegionArgumentTreesNormalizationRoute source kernel
          targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted leftChildren)
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted rightChildren)
    | lambda
        {available outer : List TypeExpr} {binder : Option String}
        {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
        (left : CostRegionTree source targetFree (domain :: available) outer
          leftBody codomain)
        (right : CostRegionTree source targetFree (domain :: available) outer
          rightBody codomain)
        (body : CostRegionTreeNormalizationRoute source kernel targetFree
          left right) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.lambda (binder := binder) left) (.lambda (binder := binder) right)
    | multiLambda
        {available outer : List TypeExpr} {arity : Nat}
        {binders : List String} {leftBody rightBody : Pattern}
        {domain codomain : TypeExpr}
        (left : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer leftBody codomain)
        (right : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer rightBody codomain)
        (body : CostRegionTreeNormalizationRoute source kernel targetFree
          left right) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.multiLambda (arity := arity) (binders := binders) left)
          (.multiLambda (arity := arity) (binders := binders) right)
    | substBody
        {available outer : List TypeExpr}
        {leftBody rightBody replacement : Pattern}
        {domain codomain : TypeExpr}
        (leftBodyTree : CostRegionTree source targetFree
          (domain :: available) outer leftBody codomain)
        (rightBodyTree : CostRegionTree source targetFree
          (domain :: available) outer rightBody codomain)
        (replacementTree : CostRegionTree source targetFree available outer
          replacement domain)
        (body : CostRegionTreeNormalizationRoute source kernel targetFree
          leftBodyTree rightBodyTree) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.subst leftBodyTree replacementTree)
          (.subst rightBodyTree replacementTree)
    | substReplacement
        {available outer : List TypeExpr}
        {bodyPattern leftReplacement rightReplacement : Pattern}
        {domain codomain : TypeExpr}
        (bodyTree : CostRegionTree source targetFree (domain :: available)
          outer bodyPattern codomain)
        (left : CostRegionTree source targetFree available outer
          leftReplacement domain)
        (right : CostRegionTree source targetFree available outer
          rightReplacement domain)
        (replacement : CostRegionTreeNormalizationRoute source kernel
          targetFree left right) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.subst bodyTree left) (.subst bodyTree right)
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {leftElements rightElements : List Pattern} {rest : Option String}
        {elementType : TypeExpr}
        (leftChildren : CostRegionElementTrees source targetFree available
          outer leftElements elementType)
        (rightChildren : CostRegionElementTrees source targetFree available
          outer rightElements elementType)
        (elements : CostRegionElementTreesNormalizationRoute source kernel
          targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationRoute source kernel targetFree
          (.collection (collectionType := collectionType) (rest := rest)
            leftChildren)
          (.collection (collectionType := collectionType) (rest := rest)
            rightChildren)

  /-- Exactly one argument of a fixed constructor carries the active route. -/
  inductive CostRegionArgumentTreesNormalizationRoute
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftArguments rightArguments : List Pattern} →
      {parameters : List TermParam} →
      CostRegionArgumentTrees source targetFree available outer leftArguments
          parameters →
      CostRegionArgumentTrees source targetFree available outer rightArguments
          parameters → Type where
    | head
        {available outer : List TypeExpr}
        {leftArgument rightArgument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (leftRepresentation :
          MatchesParameterRepresentation parameter leftArgument)
        (rightRepresentation :
          MatchesParameterRepresentation parameter rightArgument)
        (parameterType : parameterType? parameter = some expected)
        (left : CostRegionTree source targetFree available outer leftArgument
          expected)
        (right : CostRegionTree source targetFree available outer rightArgument
          expected)
        (tail : CostRegionArgumentTrees source targetFree available outer
          arguments parameters)
        (route : CostRegionTreeNormalizationRoute source kernel targetFree
          left right) :
        CostRegionArgumentTreesNormalizationRoute source kernel targetFree
          (.cons leftRepresentation parameterType left tail)
          (.cons rightRepresentation parameterType right tail)
    | tail
        {available outer : List TypeExpr} {argument : Pattern}
        {leftArguments rightArguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (representation : MatchesParameterRepresentation parameter argument)
        (parameterType : parameterType? parameter = some expected)
        (head : CostRegionTree source targetFree available outer argument
          expected)
        (left : CostRegionArgumentTrees source targetFree available outer
          leftArguments parameters)
        (right : CostRegionArgumentTrees source targetFree available outer
          rightArguments parameters)
        (route : CostRegionArgumentTreesNormalizationRoute source kernel
          targetFree left right) :
        CostRegionArgumentTreesNormalizationRoute source kernel targetFree
          (.cons representation parameterType head left)
          (.cons representation parameterType head right)

  /-- Exactly one element of a homogeneous collection carries the route. -/
  inductive CostRegionElementTreesNormalizationRoute
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftElements rightElements : List Pattern} →
      {elementType : TypeExpr} →
      CostRegionElementTrees source targetFree available outer leftElements
          elementType →
      CostRegionElementTrees source targetFree available outer rightElements
          elementType → Type where
    | head
        {available outer : List TypeExpr}
        {leftElement rightElement : Pattern} {elements : List Pattern}
        {elementType : TypeExpr}
        (left : CostRegionTree source targetFree available outer leftElement
          elementType)
        (right : CostRegionTree source targetFree available outer rightElement
          elementType)
        (tail : CostRegionElementTrees source targetFree available outer
          elements elementType)
        (route : CostRegionTreeNormalizationRoute source kernel targetFree
          left right) :
        CostRegionElementTreesNormalizationRoute source kernel targetFree
          (.cons left tail) (.cons right tail)
    | tail
        {available outer : List TypeExpr} {element : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (head : CostRegionTree source targetFree available outer element
          elementType)
        (left : CostRegionElementTrees source targetFree available outer
          leftElements elementType)
        (right : CostRegionElementTrees source targetFree available outer
          rightElements elementType)
        (route : CostRegionElementTreesNormalizationRoute source kernel
          targetFree left right) :
        CostRegionElementTreesNormalizationRoute source kernel targetFree
          (.cons head left) (.cons head right)
end

mutual
  /-- The structural prefix from the complete tree root to the static root
  where a route stops.  The context inside that static root is deliberately
  not inspected by the outer routing layer. -/
  def CostRegionTreeNormalizationRoute.activeContext
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (route : CostRegionTreeNormalizationRoute source kernel targetFree left
        right) : OneHoleContext :=
    match route with
    | .root _ => .hole
    | @CostRegionTreeNormalizationRoute.neutralApplicationOrdinary _ _ _ _ _
        rule _ _ membership _ _ _ _ _ _ _ arguments =>
        let position := arguments.activeContext
        .apply rule.label position.before position.inner
          position.after
    | @CostRegionTreeNormalizationRoute.neutralApplicationQuote _ _ _ _ _ rule
        _ _ membership _ _ _ _ _ _ _ arguments =>
        let position := arguments.activeContext
        .apply rule.label position.before position.inner
          position.after
    | @CostRegionTreeNormalizationRoute.lambda _ _ _ _ _ binder _ _ _ _ _ _
        body => .lambda binder body.activeContext
    | @CostRegionTreeNormalizationRoute.multiLambda _ _ _ _ _ arity binders _
        _ _ _ _ _ body => .multiLambda arity binders body.activeContext
    | .substBody _ _ replacement body =>
        .substBody body.activeContext replacement.sourcePattern
    | .substReplacement body _ _ replacement =>
        .substReplacement body.sourcePattern replacement.activeContext
    | @CostRegionTreeNormalizationRoute.collection _ _ _ _ _ collectionType _
        _ rest _ _ _ elements =>
        let position := elements.activeContext
        .collection collectionType position.before position.inner position.after
          rest

  /-- Exact list position of the active constructor argument. -/
  def CostRegionArgumentTreesNormalizationRoute.activeContext
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (route : CostRegionArgumentTreesNormalizationRoute source kernel
        targetFree left right) : CostPatternListRouteContext :=
    match route with
    | .head _ _ _ _ _ tail active =>
        ⟨[], active.activeContext, tail.sourcePatterns⟩
    | .tail _ _ head _ _ active =>
        let position := active.activeContext
        ⟨head.sourcePattern :: position.before, position.inner, position.after⟩

  /-- Exact list position of the active homogeneous collection element. -/
  def CostRegionElementTreesNormalizationRoute.activeContext
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (route : CostRegionElementTreesNormalizationRoute source kernel
        targetFree left right) : CostPatternListRouteContext :=
    match route with
    | .head _ _ tail active =>
        ⟨[], active.activeContext, tail.sourcePatterns⟩
    | .tail head _ _ active =>
        let position := active.activeContext
        ⟨head.sourcePattern :: position.before, position.inner, position.after⟩
end

mutual
  /-- Compact endpoints of the static root at which a route stops. -/
  def CostRegionTreeNormalizationRoute.activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (route : CostRegionTreeNormalizationRoute source kernel targetFree left
        right) : Pattern × Pattern :=
    match route with
    | .root _ => (left.sourcePattern, right.sourcePattern)
    | .neutralApplicationOrdinary _ _ _ _ _ _ _ _ arguments =>
        arguments.activePatterns
    | .neutralApplicationQuote _ _ _ _ _ _ _ _ arguments =>
        arguments.activePatterns
    | .lambda _ _ body => body.activePatterns
    | .multiLambda _ _ body => body.activePatterns
    | .substBody _ _ _ body => body.activePatterns
    | .substReplacement _ _ _ replacement => replacement.activePatterns
    | .collection _ _ elements => elements.activePatterns

  /-- Compact endpoints of the active argument subtree. -/
  def CostRegionArgumentTreesNormalizationRoute.activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (route : CostRegionArgumentTreesNormalizationRoute source kernel
        targetFree left right) : Pattern × Pattern :=
    match route with
    | .head _ _ _ _ _ _ active => active.activePatterns
    | .tail _ _ _ _ _ active => active.activePatterns

  /-- Compact endpoints of the active collection-element subtree. -/
  def CostRegionElementTreesNormalizationRoute.activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (route : CostRegionElementTreesNormalizationRoute source kernel
        targetFree left right) : Pattern × Pattern :=
    match route with
    | .head _ _ _ active => active.activePatterns
    | .tail _ _ _ active => active.activePatterns
end

mutual
  /-- The executable route prefix reconstructs both complete endpoint
  patterns when filled by its active static-root endpoint. -/
  theorem CostRegionTreeNormalizationRoute.activeContext_fill_activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (route : CostRegionTreeNormalizationRoute source kernel targetFree left
        right) :
      route.activeContext.fill route.activePatterns.1 = leftPattern ∧
        route.activeContext.fill route.activePatterns.2 = rightPattern :=
    match route with
    | .root bridge => by
        simp [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          CostRegionTree.sourcePattern]
    | .neutralApplicationOrdinary membership notBare constructor materializes
        neutral ordinary leftChildren rightChildren arguments => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          OneHoleContext.fill] using
          arguments.activeContext_fill_activePatterns
    | .neutralApplicationQuote membership notBare constructor materializes
        neutral quoted leftChildren rightChildren arguments => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          OneHoleContext.fill] using
          arguments.activeContext_fill_activePatterns
    | .lambda left right body => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          OneHoleContext.fill] using body.activeContext_fill_activePatterns
    | .multiLambda left right body => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          OneHoleContext.fill] using body.activeContext_fill_activePatterns
    | .substBody left right replacement body => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          CostRegionTree.sourcePattern, OneHoleContext.fill] using
          body.activeContext_fill_activePatterns
    | .substReplacement body left right replacement => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          CostRegionTree.sourcePattern, OneHoleContext.fill] using
          replacement.activeContext_fill_activePatterns
    | .collection left right elements => by
        simpa [CostRegionTreeNormalizationRoute.activeContext,
          CostRegionTreeNormalizationRoute.activePatterns,
          OneHoleContext.fill] using
          elements.activeContext_fill_activePatterns

  /-- The executable argument-list position reconstructs both complete
  argument lists around the active static-root endpoint. -/
  theorem CostRegionArgumentTreesNormalizationRoute.activeContext_fill_activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftPatterns rightPatterns : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftPatterns parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightPatterns parameters}
      (route : CostRegionArgumentTreesNormalizationRoute source kernel
        targetFree left right) :
      route.activeContext.before ++
          route.activeContext.inner.fill route.activePatterns.1 ::
          route.activeContext.after = leftPatterns ∧
        route.activeContext.before ++
          route.activeContext.inner.fill route.activePatterns.2 ::
          route.activeContext.after = rightPatterns :=
    match route with
    | .head leftRepresentation rightRepresentation parameterType left right
        tail active => by
        simpa [CostRegionArgumentTreesNormalizationRoute.activeContext,
          CostRegionArgumentTreesNormalizationRoute.activePatterns,
          CostRegionArgumentTrees.sourcePatterns] using
          active.activeContext_fill_activePatterns
    | .tail representation parameterType head left right active => by
        simpa [CostRegionArgumentTreesNormalizationRoute.activeContext,
          CostRegionArgumentTreesNormalizationRoute.activePatterns,
          CostRegionTree.sourcePattern, List.cons_append] using
          active.activeContext_fill_activePatterns

  /-- The executable collection-list position reconstructs both complete
  element lists around the active static-root endpoint. -/
  theorem CostRegionElementTreesNormalizationRoute.activeContext_fill_activePatterns
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftPatterns rightPatterns : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftPatterns elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightPatterns elementType}
      (route : CostRegionElementTreesNormalizationRoute source kernel
        targetFree left right) :
      route.activeContext.before ++
          route.activeContext.inner.fill route.activePatterns.1 ::
          route.activeContext.after = leftPatterns ∧
        route.activeContext.before ++
          route.activeContext.inner.fill route.activePatterns.2 ::
          route.activeContext.after = rightPatterns :=
    match route with
    | .head left right tail active => by
        simpa [CostRegionElementTreesNormalizationRoute.activeContext,
          CostRegionElementTreesNormalizationRoute.activePatterns,
          CostRegionElementTrees.sourcePatterns] using
          active.activeContext_fill_activePatterns
    | .tail head left right active => by
        simpa [CostRegionElementTreesNormalizationRoute.activeContext,
          CostRegionElementTreesNormalizationRoute.activePatterns,
          CostRegionTree.sourcePattern, List.cons_append] using
          active.activeContext_fill_activePatterns
end

/-- Proof-relevant evidence that an authored redex context passes through the
unique static root selected by a route.  `inner` is retained for later replay
inside that root rather than erased behind an existential proposition. -/
structure CostRegionTreeNormalizationRoute.Localization
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (route : CostRegionTreeNormalizationRoute source kernel targetFree left
      right)
    (context : OneHoleContext) where
  inner : OneHoleContext
  factor : context = route.activeContext.comp inner

/-- A structural one-hole context never forgets the pattern plugged into its
hole.  This local fact lets route localization recover the exact redex inside
the selected static root. -/
theorem costRouteContext_fill_injective (context : OneHoleContext) :
    Function.Injective context.fill := by
  induction context with
  | hole =>
      intro left right equality
      exact equality
  | apply constructor before inner after inductionHypothesis =>
      intro left right equality
      have argumentsEquality := (Pattern.apply.inj equality).2
      have consEquality := List.append_cancel_left argumentsEquality
      exact inductionHypothesis (List.cons.inj consEquality).1
  | lambda binderName inner inductionHypothesis =>
      intro left right equality
      exact inductionHypothesis (Pattern.lambda.inj equality).2
  | multiLambda arity binderNames inner inductionHypothesis =>
      intro left right equality
      exact inductionHypothesis (Pattern.multiLambda.inj equality).2.2
  | substBody inner replacement inductionHypothesis =>
      intro left right equality
      exact inductionHypothesis (Pattern.subst.inj equality).1
  | substReplacement body inner inductionHypothesis =>
      intro left right equality
      exact inductionHypothesis (Pattern.subst.inj equality).2
  | collection collectionType before inner after rest inductionHypothesis =>
      intro left right equality
      have elementsEquality := (Pattern.collection.inj equality).2.1
      have consEquality := List.append_cancel_left elementsEquality
      exact inductionHypothesis (List.cons.inj consEquality).1

namespace OneHoleContext

/-- The quote-visible and structural binder depths at the unique hole of a
one-hole context.  Quotation resets only the first component; binders advance
both components. -/
def canonicalizeHoleDepths (declaration : ReflectivePresentationDecl) :
    Nat -> Nat -> OneHoleContext -> Nat × Nat
  | availableDepth, scopeDepth, .hole => (availableDepth, scopeDepth)
  | availableDepth, scopeDepth,
      .apply constructor _ inner _ =>
      let childAvailableDepth :=
        if constructor == declaration.quoteConstructor then 0
        else availableDepth
      canonicalizeHoleDepths declaration childAvailableDepth scopeDepth inner
  | availableDepth, scopeDepth, .lambda _ inner =>
      canonicalizeHoleDepths declaration (availableDepth + 1)
        (scopeDepth + 1) inner
  | availableDepth, scopeDepth, .multiLambda arity _ inner =>
      canonicalizeHoleDepths declaration (availableDepth + arity)
        (scopeDepth + arity) inner
  | availableDepth, scopeDepth, .substBody inner _ =>
      canonicalizeHoleDepths declaration (availableDepth + 1)
        (scopeDepth + 1) inner
  | availableDepth, scopeDepth, .substReplacement _ inner =>
      canonicalizeHoleDepths declaration availableDepth scopeDepth inner
  | availableDepth, scopeDepth, .collection _ _ inner _ _ =>
      canonicalizeHoleDepths declaration availableDepth scopeDepth inner

/-- Equality of keyed representatives at the exact two depths selected by a
one-hole context lifts to equality of the complete filled representatives.
This is the keyed, quotation-aware companion to `canonicalize_fill_congr`. -/
theorem canonicalizeByDepths_fill_congr
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Nat -> Pattern -> Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (context : OneHoleContext)
    {left right : Pattern}
    (representatives :
      canonicalizeByDepths key declaration
          (canonicalizeHoleDepths declaration availableDepth scopeDepth
            context).1
          (canonicalizeHoleDepths declaration availableDepth scopeDepth
            context).2 left =
        canonicalizeByDepths key declaration
          (canonicalizeHoleDepths declaration availableDepth scopeDepth
            context).1
          (canonicalizeHoleDepths declaration availableDepth scopeDepth
            context).2 right) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (context.fill left) =
      canonicalizeByDepths key declaration availableDepth scopeDepth
        (context.fill right) := by
  induction context generalizing availableDepth scopeDepth with
  | hole => exact representatives
  | apply constructor before inner after inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      simp only [OneHoleContext.fill, canonicalizeByDepths,
        canonicalizeListByDepths_eq_map, List.map_append, List.map_cons,
        inductionHypothesis _ _ representatives]
  | lambda binderName inner inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      simp only [OneHoleContext.fill, canonicalizeByDepths,
        inductionHypothesis _ _ representatives]
  | multiLambda arity binderNames inner inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      simp only [OneHoleContext.fill, canonicalizeByDepths,
        inductionHypothesis _ _ representatives]
  | substBody inner replacement inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      simp only [OneHoleContext.fill, canonicalizeByDepths,
        inductionHypothesis _ _ representatives]
  | substReplacement body inner inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      simp only [OneHoleContext.fill, canonicalizeByDepths,
        inductionHypothesis _ _ representatives]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [canonicalizeHoleDepths] at representatives
      cases rest <;>
        simp only [OneHoleContext.fill, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, List.map_append, List.map_cons,
          inductionHypothesis _ _ representatives]

end OneHoleContext

namespace CostRegionTreeNormalizationRoute.Localization

/-- A localized endpoint pair reconstructs exactly the active static-root
patterns after the outer structural prefix is cancelled. -/
theorem inner_fill_eq_activePatterns
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    {route : CostRegionTreeNormalizationRoute source kernel targetFree left
      right}
    {context : OneHoleContext}
    (localization : route.Localization context)
    {redex contractum : Pattern}
    (leftEndpoint : context.fill redex = leftPattern)
    (rightEndpoint : context.fill contractum = rightPattern) :
    localization.inner.fill redex = route.activePatterns.1 ∧
      localization.inner.fill contractum = route.activePatterns.2 := by
  have reconstructed := route.activeContext_fill_activePatterns
  have redexFactor := congrArg
    (fun selected : OneHoleContext => selected.fill redex)
    localization.factor
  have contractumFactor := congrArg
    (fun selected : OneHoleContext => selected.fill contractum)
    localization.factor
  simp only [OneHoleContext.fill_comp] at redexFactor contractumFactor
  constructor
  · apply costRouteContext_fill_injective route.activeContext
    calc
      route.activeContext.fill (localization.inner.fill redex) =
          context.fill redex := redexFactor.symm
      _ = leftPattern := leftEndpoint
      _ = route.activeContext.fill route.activePatterns.1 :=
        reconstructed.1.symm
  · apply costRouteContext_fill_injective route.activeContext
    calc
      route.activeContext.fill (localization.inner.fill contractum) =
          context.fill contractum := contractumFactor.symm
      _ = rightPattern := rightEndpoint
      _ = route.activeContext.fill route.activePatterns.2 :=
        reconstructed.2.symm

end CostRegionTreeNormalizationRoute.Localization

mutual
  /-- Forget path uniqueness and obtain the full structural normalization
  alignment. -/
  def CostRegionTreeNormalizationRoute.toAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (route : CostRegionTreeNormalizationRoute source kernel targetFree left
        right) :
      CostRegionTreeNormalizationAlignment source kernel targetFree left right :=
    match route with
    | .root bridge => bridge.toTreeAlignment
    | .neutralApplicationOrdinary membership notBare constructor materializes
        neutral ordinary leftChildren rightChildren arguments =>
        .neutralApplicationOrdinary membership notBare constructor materializes
          neutral ordinary leftChildren rightChildren arguments.toAlignment
    | .neutralApplicationQuote membership notBare constructor materializes
        neutral quoted leftChildren rightChildren arguments =>
        .neutralApplicationQuote membership notBare constructor materializes
          neutral quoted leftChildren rightChildren arguments.toAlignment
    | .lambda left right body => .lambda left right body.toAlignment
    | .multiLambda left right body =>
        .multiLambda left right body.toAlignment
    | .substBody left right replacement body =>
        .subst left right replacement replacement body.toAlignment
          (.refl replacement)
    | .substReplacement body left right replacement =>
        .subst body body left right (.refl body) replacement.toAlignment
    | .collection left right elements =>
        .collection left right elements.toAlignment

  /-- Forget the unique active argument while retaining exact sibling
  reflexivity. -/
  def CostRegionArgumentTreesNormalizationRoute.toAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (route : CostRegionArgumentTreesNormalizationRoute source kernel
        targetFree left right) :
      CostRegionArgumentTreesNormalizationAlignment source kernel targetFree
        left right :=
    match route with
    | .head leftRepresentation rightRepresentation parameterType left right
        tail active =>
        .cons leftRepresentation rightRepresentation parameterType left right
          tail tail active.toAlignment
          (CostRegionArgumentTreesNormalizationAlignment.ofRefl tail)
    | .tail representation parameterType head left right active =>
        .cons representation representation parameterType head head left right
          (.refl head) active.toAlignment

  /-- Forget the unique active collection element while retaining exact
  sibling reflexivity. -/
  def CostRegionElementTreesNormalizationRoute.toAlignment
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (route : CostRegionElementTreesNormalizationRoute source kernel
        targetFree left right) :
      CostRegionElementTreesNormalizationAlignment source kernel targetFree
        left right :=
    match route with
    | .head left right tail active =>
        .cons left right tail tail active.toAlignment
          (CostRegionElementTreesNormalizationAlignment.ofRefl tail)
    | .tail head left right active =>
        .cons head head left right (.refl head) active.toAlignment
end

/-- A typed generated Cost edge with one exact active route through retained
endpoint elaborations. -/
structure CostGeneratorTreeNormalizationRoute
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right) where
  occurrence : EquationSemantics.AuthoredGeneratorWitness defaultBasePremises
    source.costWholeLanguage left.1 right.1
  erasesTo : occurrence.erase = generator
  leftElaboration : CostOpenElaboration source left
  rightElaboration : CostOpenElaboration source right
  route : CostRegionTreeNormalizationRoute source kernel targetFree
    leftElaboration.tree rightElaboration.tree
  localization : route.Localization occurrence.redexContext

namespace CostGeneratorTreeNormalizationRoute

/-- The retained occurrence really is the active local redex/contractum pair
at the static root selected by the route. -/
theorem localization_inner_fill_eq_activePatterns
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    {generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right}
    (route : CostGeneratorTreeNormalizationRoute source kernel generator) :
    route.localization.inner.fill route.occurrence.redex =
        route.route.activePatterns.1 ∧
      route.localization.inner.fill route.occurrence.contractum =
        route.route.activePatterns.2 :=
  route.localization.inner_fill_eq_activePatterns
    route.occurrence.redexContext_fill_redex
    route.occurrence.redexContext_fill_contractum

/-- Forget path uniqueness after it has certified the occurrence route. -/
def toAlignment
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right}
    (route : CostGeneratorTreeNormalizationRoute source kernel generator) :
    CostGeneratorTreeNormalizationAlignment source kernel generator where
  occurrence := route.occurrence
  erasesTo := route.erasesTo
  leftElaboration := route.leftElaboration
  rightElaboration := route.rightElaboration
  treeAlignment := route.route.toAlignment

end CostGeneratorTreeNormalizationRoute

/-- Every typed generator admits one exact active path to a semantic root
bridge.  This is stronger than tree alignability because it rules out an
unexplained collection of unrelated child changes. -/
def CostOpenGeneratorRoutable
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source) : Prop :=
  ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right),
    Nonempty (CostGeneratorTreeNormalizationRoute source kernel generator)

namespace CostOpenGeneratorRoutable

/-- Single-occurrence routing implies the previously established generic
tree-alignability obligation. -/
theorem treeAlignable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (routable : CostOpenGeneratorRoutable source kernel) :
    CostOpenGeneratorTreeAlignable source kernel := by
  intro targetFree targetBound targetSort left right generator
  obtain ⟨route⟩ := routable generator
  exact ⟨route.toAlignment⟩

/-- A total route classifier supplies the semantic normalization-span
obligation without referring to deterministic chooser coherence. -/
theorem spanLiftable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (routable : CostOpenGeneratorRoutable source kernel) :
    CostOpenGeneratorSpanLiftable source kernel.normalize :=
  CostOpenGeneratorTreeAlignable.spanLiftable routable.treeAlignable

end CostOpenGeneratorRoutable

namespace CostOpenGeneratorInvariantFor

/-- Total single-occurrence routing, vertical chooser coherence, and
agreement with the checked executor compose to exact generator invariance. -/
theorem ofRoutable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {normalizeOpen : CostOpenNormalizer source}
    (routable : CostOpenGeneratorRoutable source kernel)
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      kernel.normalize)
    (agrees : CostOpenNormalizerAgreesWithStatic source kernel.normalize
      normalizeOpen) :
    CostOpenGeneratorInvariantFor source normalizeOpen :=
  CostOpenGeneratorInvariantFor.ofTreeAlignable routable.treeAlignable coherent
    agrees

end CostOpenGeneratorInvariantFor

end Mettapedia.GSLT.LanguageDef
