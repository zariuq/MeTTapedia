import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge

/-!
# Probe of the three collapsing-leaf classifications

`CostHereditaryExposureBridge` reduces obligation B of the rho cost layer seal to
three node-local statements.  Two of them are disjunctions, and the third,
`RhoCollapsingApplyLeafBoundary`, has a single conclusion: every static node
whose declaration-coloured canonical form is an application must carry a
*certified boundary* that holds the whole canonical class.

This file refutes that third statement.

The obstruction is not a corner of the canonicalizer.  A static node's
boundaries are exactly the foreign-coloured occurrences its plan stops at, so
a plan built entirely from current-colour constructors has an empty finite
boundary table.  Canonicalization, on the other hand, turns a bare parallel
collection into the declared parallel *unit* — an application — as soon as
every element is filtered.  The two facts are independent, so they can be
satisfied at once, and then the demanded boundary does not exist.

The empty parallel `{}` at the rho process sort realises this: it is a
legitimate current-colour collection plan with no elements, hence no
boundaries, and it canonicalizes to `PZero` in *both* declaration colours.

The last section records the complementary positive fact for the two variable
routes: at the *selected* colour a certified boundary can never be the head at
which canonicalization collapses, because the only collapsing application head
is that colour's own quote constructor, whose role is `.static color` and is
therefore excluded by the boundary plan's own side condition.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## Two declaration-generic facts -/

/-- A one-entry inventory does not embed into an empty one.  The entry
embedding is order-preserving and proof-relevant, so an empty finite boundary
table admits no nonempty selection at all. -/
theorem entryEmbedding_cons_nil_elim {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {entry : TypedCostRegionBoundary source color targetFree}
    {small : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      (entry :: small) []) : False := by
  cases embedding

/-- The empty parallel collection canonicalizes to the declared parallel unit,
which is a canonical application.  Stated for an arbitrary reflective
declaration whose parallel collection is the rho bag. -/
theorem canonicalize_emptyParallel_eq_canonicalize_unit
    (declaration : ReflectivePresentationDecl)
    (parallel : declaration.parallelCollection = .hashBag)
    (unitNe : declaration.parallelUnitConstructor ≠
      declaration.quoteConstructor) :
    canonicalize declaration (.collection .hashBag [] none) =
      canonicalize declaration
        (.apply declaration.parallelUnitConstructor []) := by
  rw [← parallel, canonicalize_parallel,
    canonicalize_apply_of_ne_quote declaration unitNe]
  simp [normalizeParallelElements, collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

/-- Colouring renames constructors but not collection types, so the declared
parallel collection is the rho bag in either declaration colour. -/
theorem rhoDecl_parallelCollection (declarationColor : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelCollection = .hashBag := by
  cases declarationColor <;> rfl

/-- The declared parallel unit is not the declared quote, in either colour. -/
theorem rhoDecl_unit_ne_quote (declarationColor : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelUnitConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor := by
  cases declarationColor <;> decide

/-! ## A boundary-free static node whose canonical form is an application -/

theorem rhoParallelRule_mem :
    rhoCalc.terms[3] ∈
      rhoCIGSLT.theory.presentation.presentation.language.terms := by
  change rhoCalc.terms[3] ∈ rhoCalc.terms
  simp [rhoCalc]

/-- The bare-collection typing choice presenting the rho parallel
constructor. -/
def rhoParallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

theorem rhoParallelChoice_mem :
    rhoParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base rhoProc.1)) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, rhoParallelRule_mem,
    ?_, rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ rhoParallelRule_mem
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

/-- The empty parallel as a current-colour collection plan.  Its element plan
is `nil`, so the plan stops at no foreign occurrence. -/
def rhoEmptyParallelPlan :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base [])
      [] (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole (.collection .hashBag [] none) (.base rhoProc.1) :=
  .collection rhoParallelChoice rhoParallelChoice_mem .nil

/-- The empty parallel in the generated base process fibre. -/
def rhoEmptyParallelTerm :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) := by
  refine ⟨.collection .hashBag [] none, ⟨?_, rfl, rfl, rfl⟩, ?_⟩
  · apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
    · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ rhoParallelRule_mem
    · exact rho_costBaseParallelConstructor_params
    · exact .nil [] _
  · intro presentation membership
    rfl

/-- The static region node carrying the empty parallel. -/
def rhoEmptyParallelNode :
    CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan rhoEmptyParallelTerm.toCore rhoEmptyParallelPlan
    rfl

@[simp]
theorem rhoEmptyParallelNode_term :
    rhoEmptyParallelNode.term.1 = .collection .hashBag [] none := rfl

@[simp]
theorem rhoEmptyParallelNode_skeleton :
    rhoEmptyParallelNode.skeleton.1 = .collection .hashBag [] none := rfl

@[simp]
theorem rhoEmptyParallelNode_targetBound :
    rhoEmptyParallelNode.targetBound = [] := rfl

/-- **The node has no boundaries.**  Its plan is a current-colour collection
with an empty element spine, so the finite boundary table is empty. -/
@[simp]
theorem rhoEmptyParallelNode_entries :
    rhoEmptyParallelNode.finiteBoundaryTable.entries = [] := rfl

/-- The witness is not merely a well-formed node record: it is the node of an
actual region tree. -/
def rhoEmptyParallelTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc).1) :=
  .static rhoEmptyParallelNode .nil

/-- …and it is exposed by a static root view, which is exactly the shape in
which `rho_collapsingLeafExposureApplyRoute_of_boundary` feeds a node to
`RhoCollapsingApplyLeafBoundary`. -/
def rhoEmptyParallelView : rhoEmptyParallelTree.StaticRootView .base where
  node := rhoEmptyParallelNode
  children := .nil
  patternEq := rfl
  availableEq := rfl
  typeEq := rfl
  treeEq := rfl

@[simp]
theorem rhoEmptyParallelView_node :
    rhoEmptyParallelView.node = rhoEmptyParallelNode := rfl

/-- The node's root is a collapsing root for either declaration colour: it is
a bare collection at the declared parallel type. -/
theorem rhoEmptyParallelNode_collapsingRoot (declarationColor : CostStaticColor) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rhoEmptyParallelNode.term.1 :=
  Or.inr ⟨[], by rw [rhoEmptyParallelNode_term, rhoDecl_parallelCollection]⟩

/-- The node's declaration-coloured canonical form is an application: the
declared parallel unit. -/
theorem rhoEmptyParallelNode_canonical (declarationColor : CostStaticColor) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rhoEmptyParallelNode.term.1 =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelUnitConstructor []) := by
  rw [rhoEmptyParallelNode_term]
  exact canonicalize_emptyParallel_eq_canonicalize_unit _
    (rhoDecl_parallelCollection declarationColor)
    (rhoDecl_unit_ne_quote declarationColor)

/-! ## The application classification is false -/

/-- **The general obstruction.**  A static node with an empty finite boundary
table refutes `RhoCollapsingApplyLeafBoundary` as soon as it satisfies that
statement's two hypotheses, because the demanded entry embedding selects one
entry from an empty inventory. -/
theorem not_rhoCollapsingApplyLeafBoundary_of_entries_eq_nil
    {declarationColor color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (entriesNil : node.finiteBoundaryTable.entries = [])
    {label : String} {arguments : List Pattern}
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      node.term.1)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments)) :
    ¬ RhoCollapsingApplyLeafBoundary declarationColor := by
  intro boundary
  obtain ⟨_payload, _state, ⟨embedding⟩, _, _, _, _⟩ :=
    boundary node collapsing canonical
  rw [entriesNil] at embedding
  exact entryEmbedding_cons_nil_elim embedding

/-- **`RhoCollapsingApplyLeafBoundary` is false, at both declaration
colours.**

The witness is the empty parallel at the rho process sort.  It is a genuine
current-colour static root, it collapses under either declaration colour, its
canonical form is the declared parallel unit — an application — and its plan
stops at nothing, so there is no certified boundary to produce. -/
theorem not_rhoCollapsingApplyLeafBoundary (declarationColor : CostStaticColor) :
    ¬ RhoCollapsingApplyLeafBoundary declarationColor :=
  not_rhoCollapsingApplyLeafBoundary_of_entries_eq_nil rhoEmptyParallelNode
    rhoEmptyParallelNode_entries
    (rhoEmptyParallelNode_collapsingRoot declarationColor)
    (rhoEmptyParallelNode_canonical declarationColor)

/-- **The three classifications are jointly uninhabited.**

`rho_collapsingLeaf_hasExposure_of_classifications` therefore cannot be
applied: its third hypothesis has no inhabitant.  The reduction is sound but
vacuous as stated, so obligation B is not reachable through it. -/
theorem not_rhoCollapsingLeafClassifications (declarationColor : CostStaticColor) :
    ¬ (RhoCollapsingBVarLeafDichotomy declarationColor ∧
        RhoCollapsingFVarLeafDichotomy declarationColor ∧
        RhoCollapsingApplyLeafBoundary declarationColor) :=
  fun classifications =>
    not_rhoCollapsingApplyLeafBoundary declarationColor classifications.2.2

/-! ## At the selected colour a boundary is never the collapsing head

The two variable classifications each offer a boundary arm.  This section
shows that arm is unavailable whenever the declaration colour is the node's
own colour: the only application head at which canonicalization collapses is
that colour's quote constructor, and its role is `.static color`, which is
exactly what a foreign-boundary plan excludes.  So at the selected colour the
whole bound- or free-variable canonical class must be carried by the
skeleton-static arm.
-/

/-- The rho quote is a wrapped-fragment constructor: it is neither interaction
principal. -/
theorem rhoQuote_mem_wrappedConstructors :
    rhoQuoteConstructor ∈ rhoCIGSLT.continuationRetyping.wrappedConstructors :=
  (rhoCIGSLT.continuationRetyping.mem_wrappedConstructors_iff
    rhoQuoteConstructor).2 (by
      constructor
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide)
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide))

/-- The exact declared Cost constructor presenting one colour's quote. -/
def rhoQuoteDeclared : CostStaticColor → rhoCIGSLT.DeclaredCostConstructor
  | .base => ⟨.base rhoQuoteConstructor, True.intro⟩
  | .wrapped => ⟨.wrapped rhoQuoteConstructor, rhoQuote_mem_wrappedConstructors⟩

theorem rhoQuoteDeclared_role (color : CostStaticColor) :
    rhoCIGSLT.declaredCostConstructorRole (rhoQuoteDeclared color) =
      .static color := by
  cases color <;> rfl

theorem rhoQuoteDeclared_render (color : CostStaticColor) :
    rhoCIGSLT.renderDeclaredCostConstructor (rhoQuoteDeclared color) =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  cases color <;> rfl

/-- Only a colour's own quote renders to that colour's declared quote name,
and its role is that colour's static role. -/
theorem rhoRole_static_of_render_eq_quote {color : CostStaticColor}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor) :
    rhoCIGSLT.declaredCostConstructorRole constructor = .static color := by
  have equality : constructor = rhoQuoteDeclared color :=
    rhoCIGSLT.renderDeclaredCostConstructor_injective
      (rendered.trans (rhoQuoteDeclared_render color).symm)
  rw [equality, rhoQuoteDeclared_role]

/-- A collapsing application root is headed by the declared quote. -/
theorem eq_quoteConstructor_of_collapsingRoot_apply
    (declaration : ReflectivePresentationDecl) {wireName : String}
    {arguments : List Pattern}
    (collapsing : CollapsingRoot declaration (.apply wireName arguments)) :
    wireName = declaration.quoteConstructor := by
  rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
  · exact (Pattern.apply.inj shape).1
  · exact absurd shape (by simp)

/-- **A selected-colour foreign boundary is never a collapsing root.** -/
theorem not_collapsingRoot_of_boundaryHead {color : CostStaticColor}
    {wireName : String} {arguments : List Pattern}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (outsideCurrent : rhoCIGSLT.declaredCostConstructorRole constructor ≠
      .static color) :
    ¬ CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) :=
  fun collapsing =>
    outsideCurrent
      (rhoRole_static_of_render_eq_quote constructor
        (rendered.trans (eq_quoteConstructor_of_collapsingRoot_apply _ collapsing)))

/-- Selected-colour boundary content never canonicalizes to a bound
variable. -/
theorem boundaryHead_canonicalize_ne_bvar {color : CostStaticColor}
    {wireName : String} {arguments : List Pattern} {index : Nat}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (outsideCurrent : rhoCIGSLT.declaredCostConstructorRole constructor ≠
      .static color) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) ≠ .bvar index := by
  intro collapsed
  rcases eq_bvar_or_collapsingRoot_of_canonicalize_eq_bvar _ collapsed with
    shape | collapsing
  · exact absurd shape (by simp)
  · exact not_collapsingRoot_of_boundaryHead constructor rendered outsideCurrent
      collapsing

/-- Selected-colour boundary content never canonicalizes to a free
variable. -/
theorem boundaryHead_canonicalize_ne_fvar {color : CostStaticColor}
    {wireName : String} {arguments : List Pattern} {name : String}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (outsideCurrent : rhoCIGSLT.declaredCostConstructorRole constructor ≠
      .static color) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) ≠ .fvar name := by
  intro collapsed
  rcases eq_fvar_or_collapsingRoot_of_canonicalize_eq_fvar _ collapsed with
    shape | collapsing
  · exact absurd shape (by simp)
  · exact not_collapsingRoot_of_boundaryHead constructor rendered outsideCurrent
      collapsing

/-- **Plan form.**  A selected-colour plan whose application pattern
canonicalizes to a bound variable is a current-colour static root, never a
foreign boundary. -/
theorem isStaticRoot_of_canonicalize_eq_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {arguments : List Pattern} {sourceType : TypeExpr}
    {index : Nat}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer (.apply wireName arguments)
      sourceType)
    (collapsed : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) = .bvar index) :
    plan.isStaticRoot = true := by
  cases plan with
  | boundaryApplication constructor rendered outsideCurrent _ _ =>
      exact absurd collapsed
        (boundaryHead_canonicalize_ne_bvar constructor rendered outsideCurrent)
  | application => rfl

/-! ### The boundary-content emptiness lemma

`certifyCostRegionBoundary?` itself checks only two things: that the observed
target type decodes in the selected colour, and that the content is
well-sorted at that type.  It does not see a constructor's role.  The role
side condition lives in the *plan*: `boundaryApplication` carries
`outsideCurrent`, and `boundaryCollection` carries the rejection of the whole
current-colour typing-choice family.  So the emptiness statement has to be
made about plan boundaries, and that is what the two theorems below do.

Together they say: at a rho process-typed position and the selected colour,
no plan boundary's content canonicalizes to a bare bound variable — or to a
bare free variable.  The application half is the role contradiction proved
above; the collection half is the disjointness of the two process fibres. -/

/-- A rho process-typed collection plan is a current-colour static root; it is
never an opposite-colour collection boundary. -/
theorem isStaticRoot_of_rhoProcess_collection
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern} {rest : Option String}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements rest)
      (.base rhoCIGSLT.theory.presentation.interactingSort.1.name)) :
    plan.isStaticRoot = true := by
  obtain ⟨choice, selected⟩ :=
    CostStaticRegionPlan.exists_currentChoice_of_rhoProcess_collection plan
  exact CostStaticRegionPlan.isStaticRoot_of_current_collection plan choice
    selected

/-- **Boundary-content emptiness, bound-variable form.**

At the selected colour and the rho process type, a plan whose content
canonicalizes to a bare bound variable is a current-colour static root or the
bound-variable plan itself.  Neither carries a certified boundary, so the
`(certified boundary, bound-variable)` configuration is uninhabited there. -/
theorem isStaticRoot_or_bvar_of_rhoProcess_canonicalize_eq_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {content : Pattern} {sourceType : TypeExpr} {index : Nat}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer content sourceType)
    (processType : sourceType =
      .base rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (collapsed : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        content = .bvar index) :
    plan.isStaticRoot = true ∨ ∃ sourceIndex : Nat, content = .bvar sourceIndex := by
  generalize hty : TypeExpr.base
    rhoCIGSLT.theory.presentation.interactingSort.1.name = ty at plan
  cases plan with
  | bvar => exact Or.inr ⟨_, rfl⟩
  | fvar => exact absurd collapsed (by simp [canonicalize])
  | boundaryApplication constructor rendered outsideCurrent _ _ =>
      exact absurd collapsed
        (boundaryHead_canonicalize_ne_bvar constructor rendered outsideCurrent)
  | application => exact Or.inl rfl
  | lambda => exact absurd processType (by simp)
  | multiLambda => exact absurd processType (by simp)
  | collection => exact Or.inl rfl
  | boundaryCollection _ oppositeChoice oppositeSelected _ _ =>
      subst processType
      rw [rho_costStaticCollectionTypingChoices_flip_mappedProcess_eq_nil]
        at oppositeSelected
      simp at oppositeSelected

/-- **Boundary-content emptiness, free-variable form.** -/
theorem isStaticRoot_or_fvar_of_rhoProcess_canonicalize_eq_fvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {content : Pattern} {sourceType : TypeExpr} {name : String}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer content sourceType)
    (processType : sourceType =
      .base rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (collapsed : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        content = .fvar name) :
    plan.isStaticRoot = true ∨ ∃ sourceName : String, content = .fvar sourceName := by
  generalize hty : TypeExpr.base
    rhoCIGSLT.theory.presentation.interactingSort.1.name = ty at plan
  cases plan with
  | bvar => exact absurd collapsed (by simp [canonicalize])
  | fvar => exact Or.inr ⟨_, rfl⟩
  | boundaryApplication constructor rendered outsideCurrent _ _ =>
      exact absurd collapsed
        (boundaryHead_canonicalize_ne_fvar constructor rendered outsideCurrent)
  | application => exact Or.inl rfl
  | lambda => exact absurd processType (by simp)
  | multiLambda => exact absurd processType (by simp)
  | collection => exact Or.inl rfl
  | boundaryCollection _ oppositeChoice oppositeSelected _ _ =>
      subst processType
      rw [rho_costStaticCollectionTypingChoices_flip_mappedProcess_eq_nil]
        at oppositeSelected
      simp at oppositeSelected

/-! ### Why the selected-colour argument does not extend to the opposite colour

At the opposite declaration colour the role contradiction above evaporates:
the collapsing head is then the *other* colour's quote, whose role is
`.static declarationColor`, which the boundary side condition permits.  What
remains is a sorting question, and the two rho sorts answer it differently.
The process sorts of the two static fibres are disjoint, so no opposite-colour
constructor can sit at a process-typed boundary; but the name sort is shared,
so an opposite-colour quote *is* correctly sorted at a name-typed boundary.
Both facts are recorded here because they decide where the remaining search
has to go. -/

/-- The two static fibres share the rho name sort. -/
theorem rhoName_shared_across_colors :
    mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT) (.base "Name") =
      mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Name") := by
  decide

/-- The two static fibres do not share the rho process sort. -/
theorem rhoProc_not_shared_across_colors :
    mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT) (.base "Proc") ≠
      mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Proc") := by
  decide

/-- Free-variable companion of `isStaticRoot_of_canonicalize_eq_bvar`. -/
theorem isStaticRoot_of_canonicalize_eq_fvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {arguments : List Pattern} {sourceType : TypeExpr}
    {name : String}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer (.apply wireName arguments)
      sourceType)
    (collapsed : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) = .fvar name) :
    plan.isStaticRoot = true := by
  cases plan with
  | boundaryApplication constructor rendered outsideCurrent _ _ =>
      exact absurd collapsed
        (boundaryHead_canonicalize_ne_fvar constructor rendered outsideCurrent)
  | application => rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
