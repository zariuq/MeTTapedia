import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
import Mettapedia.GSLT.LanguageDef.CostStaticPlanStoppedShape

/-!
# Shape closure for the collapsing-leaf application route

Work in progress.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

/-- A neutral declared constructor never carries a static role. -/
theorem role_ne_static_of_neutral {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (neutral : rhoCIGSLT.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, rhoCIGSLT.declaredCostConstructorRole constructor =
        .apparatus kind) :
    rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color := by
  rcases neutral with principal | ⟨kind, apparatus⟩
  · rw [principal]; exact fun h => by cases h
  · rw [apparatus]; exact fun h => by cases h

/-- **A neutral head is never a declared quote.**  The rendered wire name of a
neutral declared constructor differs from every colour's declared quote
constructor, because only that colour's own quote renders to it and its role is
that colour's static role. -/
theorem render_ne_quoteConstructor_of_neutral {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (neutral : rhoCIGSLT.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, rhoCIGSLT.declaredCostConstructorRole constructor =
        .apparatus kind) :
    rhoCIGSLT.renderDeclaredCostConstructor constructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor :=
  fun rendered =>
    role_ne_static_of_neutral (color := color) neutral
      (rhoRole_static_of_render_eq_quote constructor rendered)

/-- Wire form of `render_ne_quoteConstructor_of_neutral`: the materialized
rule of a neutral declared constructor is not labelled by a declared quote. -/
theorem label_ne_quoteConstructor_of_neutral {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor} {rule : GrammarRule}
    (materializes :
      rhoCIGSLT.materializeDeclaredCostConstructor constructor = rule)
    (neutral : rhoCIGSLT.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, rhoCIGSLT.declaredCostConstructorRole constructor =
        .apparatus kind) :
    rule.label ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  subst materializes
  rw [rhoCIGSLT.materializeDeclaredCostConstructor_label]
  exact render_ne_quoteConstructor_of_neutral neutral

/-- **A retained application endpoint never collapses.**

The application route's partner is a neutral constructor application, so its
wire head is not the declaration's quote and canonicalization only descends
into the arguments.  This is the premise separating the route from the refuted
`RhoCollapsingApplyLeafBoundary`, which quantified over an arbitrary
application pattern with no endpoint at all. -/
theorem canonicalize_apply_of_structural
    {declarationColor : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {label : String}
    {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments) =
      .apply label
        (arguments.map (canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl))) := by
  cases other.structuralRootView structural with
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral _ordinary _children =>
      exact canonicalize_apply_of_ne_quote _
        (label_ne_quoteConstructor_of_neutral materializes neutral) _
  | neutralApplicationQuote membership notBare constructor materializes
      neutral _quoted _children =>
      exact canonicalize_apply_of_ne_quote _
        (label_ne_quoteConstructor_of_neutral materializes neutral) _

/-! ## The declared parallel unit is a static head

`RhoCollapsingApplyLeafBoundary` is refuted by the empty parallel, whose
declaration-coloured canonical form is the declared parallel unit.  The route
retains the partner endpoint, and this section shows the unit is unreachable
there: only a colour's own `PZero` renders to that colour's declared unit, and
its role is that colour's static role, which a retained endpoint excludes. -/

/-- The exact rho nullary process constructor. -/
def rhoZeroConstructor :
    StructuralMorphism.AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[0], List.getElem_mem (by simp [rhoCalc])⟩

/-- `PZero` is a wrapped-fragment constructor: it is neither interaction
principal. -/
theorem rhoZero_mem_wrappedConstructors :
    rhoZeroConstructor ∈ rhoCIGSLT.continuationRetyping.wrappedConstructors :=
  (rhoCIGSLT.continuationRetyping.mem_wrappedConstructors_iff
    rhoZeroConstructor).2 (by
      constructor
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide)
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide))

/-- The exact declared Cost constructor presenting one colour's unit. -/
def rhoZeroDeclared : CostStaticColor → rhoCIGSLT.DeclaredCostConstructor
  | .base => ⟨.base rhoZeroConstructor, True.intro⟩
  | .wrapped => ⟨.wrapped rhoZeroConstructor, rhoZero_mem_wrappedConstructors⟩

theorem rhoZeroDeclared_role (color : CostStaticColor) :
    rhoCIGSLT.declaredCostConstructorRole (rhoZeroDeclared color) =
      .static color := by
  cases color <;> rfl

theorem rhoZeroDeclared_render (color : CostStaticColor) :
    rhoCIGSLT.renderDeclaredCostConstructor (rhoZeroDeclared color) =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor := by
  cases color <;> rfl

/-- Only a colour's own unit renders to that colour's declared parallel unit,
and its role is that colour's static role. -/
theorem rhoRole_static_of_render_eq_parallelUnit {color : CostStaticColor}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor) :
    rhoCIGSLT.declaredCostConstructorRole constructor = .static color := by
  have equality : constructor = rhoZeroDeclared color :=
    rhoCIGSLT.renderDeclaredCostConstructor_injective
      (rendered.trans (rhoZeroDeclared_render color).symm)
  rw [equality, rhoZeroDeclared_role]

/-- Wire form: the materialized rule of a neutral declared constructor is not
labelled by a declared parallel unit. -/
theorem label_ne_parallelUnit_of_neutral {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor} {rule : GrammarRule}
    (materializes :
      rhoCIGSLT.materializeDeclaredCostConstructor constructor = rule)
    (neutral : rhoCIGSLT.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, rhoCIGSLT.declaredCostConstructorRole constructor =
        .apparatus kind) :
    rule.label ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor := by
  subst materializes
  rw [rhoCIGSLT.materializeDeclaredCostConstructor_label]
  exact fun rendered =>
    role_ne_static_of_neutral (color := color) neutral
      (rhoRole_static_of_render_eq_parallelUnit constructor rendered)

/-- **A retained application endpoint is never the declared unit.** -/
theorem label_ne_parallelUnit_of_structural
    {declarationColor : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {label : String}
    {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false) :
    label ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor := by
  cases other.structuralRootView structural with
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral _ordinary _children =>
      exact label_ne_parallelUnit_of_neutral materializes neutral
  | neutralApplicationQuote membership notBare constructor materializes
      neutral _quoted _children =>
      exact label_ne_parallelUnit_of_neutral materializes neutral

/-- **The empty-parallel refutation does not transfer to the route.**

`not_rhoCollapsingApplyLeafBoundary` refutes the application *classification*
with the empty parallel, whose declaration-coloured canonical form is the
declared parallel unit.  `RhoCollapsingLeafExposureApplyRoute` retains the
partner endpoint together with `other.rootIsStatic = false`, and no such
endpoint canonicalizes to the unit: its head is neutral, whereas the unit is
its colour's own static constructor.  So the whole refuting configuration is
absent from the route — the route is not refuted by the witness that kills the
classification. -/
theorem no_structural_partner_of_emptyParallel
    {declarationColor : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {label : String}
    {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.collection .hashBag [] none) =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.apply label arguments)) : False := by
  have unitEq := canonicalize_emptyParallel_eq_canonicalize_unit
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation.toReflectivePresentationDecl)
    (rhoDecl_parallelCollection declarationColor)
    (rhoDecl_unit_ne_quote declarationColor)
  rw [unitEq, canonicalize_apply_of_ne_quote _
      (rhoDecl_unit_ne_quote declarationColor) [],
    canonicalize_apply_of_structural (declarationColor := declarationColor)
      other structural] at canonical
  exact label_ne_parallelUnit_of_structural (declarationColor := declarationColor)
    other structural (Pattern.apply.inj canonical).1.symm

/-! ## No retained endpoint sits in the rho name fibre

A retained application endpoint is headed by a neutral declared constructor,
and the neutral fragment of the rho Cost signature is exactly the two
interaction principals — both process constructors — together with the fixed
apparatus, whose categories are the two apparatus sorts and the wrapped
carrier.  None of them is the rho name sort, which both colours send to the
same base-tagged carrier.  So the application route has no partner at all when
the collapsed static node's source sort is `Name`. -/

/-- The rho cut's program principal is a process constructor. -/
theorem rhoCut_program_category :
    (rhoCIGSLT.cut.program.constructor).1.category = "Proc" := rfl

/-- The rho cut's environment principal is a process constructor. -/
theorem rhoCut_environment_category :
    (rhoCIGSLT.cut.environment.constructor).1.category = "Proc" := rfl

/-- **The neutral fragment avoids the rho name sort.** -/
theorem materialize_category_ne_name
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (neutral : rhoCIGSLT.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, rhoCIGSLT.declaredCostConstructorRole constructor =
        .apparatus kind) :
    (rhoCIGSLT.materializeDeclaredCostConstructor constructor).category ≠
      costBaseSortName "Name" := by
  obtain ⟨generated, declared⟩ := constructor
  cases generated with
  | base sourceConstructor =>
      have principal : sourceConstructor = rhoCIGSLT.cut.program.constructor ∨
          sourceConstructor = rhoCIGSLT.cut.environment.constructor := by
        by_contra notPrincipal
        have role : rhoCIGSLT.declaredCostConstructorRole
            ⟨.base sourceConstructor, declared⟩ = .static .base := by
          simp [CIGSLT.declaredCostConstructorRole, notPrincipal]
        rcases neutral with equality | ⟨kind, equality⟩ <;>
          rw [role] at equality <;> cases equality
      have category : sourceConstructor.1.category = "Proc" := by
        rcases principal with equality | equality <;> rw [equality]
        · exact rhoCut_program_category
        · exact rhoCut_environment_category
      show costBaseSortName sourceConstructor.1.category ≠ _
      rw [category]
      exact fun equality =>
        absurd (costBaseSortName_injective equality) (by decide)
  | wrapped sourceConstructor =>
      have role : rhoCIGSLT.declaredCostConstructorRole
          ⟨.wrapped sourceConstructor, declared⟩ = .static .wrapped := rfl
      rcases neutral with equality | ⟨kind, equality⟩ <;>
        rw [role] at equality <;> cases equality
  | apparatus kind =>
      have category : (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨.apparatus kind, declared⟩).category =
          (kind.grammarRule
            rhoCIGSLT.theory.presentation.interactingSort.1.name).category :=
        rfl
      rw [category]
      cases kind
      · exact (costBaseSortName_ne_apparatus "Name" "signature").symm
      · exact (costBaseSortName_ne_apparatus "Name" "signature").symm
      · exact (costBaseSortName_ne_wrapped "Name").symm
      · exact (costBaseSortName_ne_apparatus "Name" "token-stack").symm
      · exact (costBaseSortName_ne_apparatus "Name" "token-stack").symm
      · exact (costBaseSortName_ne_wrapped "Name").symm
      · exact (costBaseSortName_ne_wrapped "Name").symm

/-- Both static colours send the rho name sort to the same base carrier. -/
theorem mapLangSort_rhoName (color : CostStaticColor) :
    (color.mapLangSort rhoCIGSLT rhoName).1 = costBaseSortName "Name" := by
  cases color <;> rfl

/-- **A retained application endpoint never inhabits the rho name fibre.** -/
theorem no_structural_apply_of_type_eq_name
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false)
    (nameFibre : type = .base (costBaseSortName "Name")) : False := by
  cases other.structuralRootView structural with
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral _ordinary _children =>
      exact materialize_category_ne_name neutral
        (by rw [materializes]; exact TypeExpr.base.inj nameFibre)
  | neutralApplicationQuote membership notBare constructor materializes
      neutral _quoted _children =>
      exact materialize_category_ne_name neutral
        (by rw [materializes]; exact TypeExpr.base.inj nameFibre)

/-- Colour-indexed form: the rho name fibre of either static colour retains no
application endpoint. -/
theorem no_structural_apply_at_rhoName {color : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {label : String} {arguments : List Pattern}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments)
      (.base (color.mapLangSort rhoCIGSLT rhoName).1))
    (structural : other.rootIsStatic = false) : False :=
  no_structural_apply_of_type_eq_name other structural
    (by rw [mapLangSort_rhoName])

/-! ## Which collapsing shells evaporate under canonicalization

`stoppedCollapseOfCloseSmaller` asks for `contextCollapse`: the retained
skeleton context, filled with the stopped boundary's rigid variable, must
canonicalize back to that variable.  The two syntactic shapes of
`CollapsingRoot` answer this differently, and the difference decides which
exposure route each shape can use. -/

/-- **A singleton parallel shell evaporates.**  Splicing leaves the single
element, unit filtering does not remove a variable, and the singleton branch
of `collapseParallel` returns it. -/
theorem canonicalize_singletonParallel_fvar (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [.fvar name] none) = .fvar name := by
  simp [canonicalize, canonicalizeList, normalizeParallelElements,
    collapseParallel, parallelSplice,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

/-- **A quote shell over a bare variable does not evaporate.**  Quote-drop
fires only on a drop argument, so the shell survives canonicalization.

Consequently the quote shape of `CollapsingRoot` cannot meet `contextCollapse`
with a plain boundary variable: its exposure must come from the drop-carrying
route rather than the parallel-singleton one. -/
theorem canonicalize_quote_fvar_ne (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        [.fvar name]) ≠ .fvar name := by
  simp [canonicalize, canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- **A quote shell over a drop does evaporate.**  Quote-drop fires and
returns the dropped name, so the quote shape meets `contextCollapse` exactly
when its boundary carries the drop.

With the two theorems above this settles `contextCollapse` for both syntactic
shapes of `CollapsingRoot`: the parallel shape needs a singleton, the quote
shape needs a drop, and a quote over a bare variable is excluded. -/
theorem canonicalize_quote_drop_fvar (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        [.apply
          rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
          [.fvar name]]) = .fvar name := by
  simp [canonicalize, canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- **The empty parallel canonicalizes to the unit.**  Nothing survives the
splice, so `collapseParallel` takes its nil branch.

This is why the empty shape admits no stopped boundary at all: there is no
element to certify, hence no rigid variable for `contextCollapse` to return.
It is excluded from the exposure route rather than served by it, and is the
shape `no_structural_partner_of_emptyParallel` above governs. -/
theorem canonicalize_emptyParallel :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      (.collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [] none) =
      .apply rhoReflectivePresentation.parallelUnitConstructor [] := by
  simp [canonicalize, canonicalizeList, normalizeParallelElements,
    collapseParallel, Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

/-- **A static root view's plan classifies at any decomposition.**

`CostStaticPlanContextView` has exactly the two cases `.stopped` and
`.reached`, and `nonempty_shapedContextView` produces one for any plan and any
`pattern = context.fill payload` with no further side conditions.  Exposed
here at the static-root-view level, which is where the exposure routes consume
it: the stopped certificate that `stoppedCollapseOfCloseSmaller` requires need
not be constructed by hand, and the reached alternative is what the deep-atom
route serves. -/
theorem nonempty_planStopped_or_planReached
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (payload : Pattern)
    (fillEq : leftView.node.term.1 = context.fill payload) :
    Nonempty (CostStaticPlanStopped rhoCIGSLT color targetFree payload
        leftView.node.plan.abstractPattern) ∨
      Nonempty (CostStaticPlanReached rhoCIGSLT color targetFree payload
        leftView.node.plan.abstractPattern) := by
  obtain ⟨⟨view, _shape⟩⟩ :=
    leftView.node.plan.nonempty_shapedContextView context fillEq
  cases view with
  | stopped state => exact .inl ⟨state⟩
  | reached state => exact .inr ⟨state⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure
