import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

/-!
# Quote/Drop collapse agreement at a foreign canonicalizer

The source canonicalizer collapses `Quote [Drop [n]]` to `n`.  A paired
authored-Quote stop is admitted only when its two payloads are canonically
equal at the *foreign* declaration, where the view colour's quote and drop
wires are rigid.  These results measure whether the two sides can therefore
choose different collapse outcomes.
-/

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace QuoteDropCollapse

/-- The view colour's quote wire is rigid at any other colour's declaration. -/
theorem viewQuote_ne_foreignQuote {declarationColor viewColor : CostStaticColor}
    (different : declarationColor ≠ viewColor) :
    (viewColor.symbols rhoCIGSLT).constructor "NQuote" ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  rw [rhoDecl_quoteConstructor]
  cases declarationColor <;> cases viewColor <;> first
    | exact absurd rfl different
    | decide

/-- The view colour's drop wire is rigid at any colour's declaration. -/
theorem viewDrop_ne_foreignQuote {declarationColor viewColor : CostStaticColor} :
    (viewColor.symbols rhoCIGSLT).constructor "PDrop" ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  rw [rhoDecl_quoteConstructor]
  cases declarationColor <;> cases viewColor <;> decide

/-- Abbreviation for the foreign canonicalizer of a paired stop. -/
private abbrev foreignDecl (declarationColor : CostStaticColor) :
    ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
    rhoReflectivePresentation.toReflectivePresentationDecl

/-- **The differential collapse witness is not admissible.**  The payload pair
`Quote (Drop (Quote z))` against `Quote z`, written with the view colour's
wires, is never canonically equal at a foreign declaration, so it cannot
satisfy the raw-stop premise of a paired authored-Quote alignment. -/
theorem quoteDropQuote_ne_quote_at_foreign
    {declarationColor viewColor : CostStaticColor}
    (different : declarationColor ≠ viewColor) (inner : Pattern) :
    canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
          [.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
            [.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
              [inner]]]) ≠
      canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
          [.bvar 0]) := by
  have leftCanon : canonicalize (foreignDecl declarationColor)
      (.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
        [.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
          [.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
            [inner]]]) =
      .apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
        [.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
          [.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
            [canonicalize (foreignDecl declarationColor) inner]]] := by
    rw [canonicalize_apply_of_ne_quote _ (viewQuote_ne_foreignQuote different)]
    simp only [List.map_cons, List.map_nil]
    rw [canonicalize_apply_of_ne_quote _
      (viewDrop_ne_foreignQuote (declarationColor := declarationColor))]
    simp only [List.map_cons, List.map_nil]
    rw [canonicalize_apply_of_ne_quote _ (viewQuote_ne_foreignQuote different)]
    simp only [List.map_cons, List.map_nil]
  have rightCanon : canonicalize (foreignDecl declarationColor)
      (.apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
        [.bvar 0]) =
      .apply ((viewColor.symbols rhoCIGSLT).constructor "NQuote")
        [.bvar 0] := by
    rw [canonicalize_apply_of_ne_quote _ (viewQuote_ne_foreignQuote different)]
    simp only [List.map_cons, List.map_nil, canonicalize]
  rw [leftCanon, rightCanon]
  intro equal
  have arguments := (Pattern.apply.inj equal).2
  simp only [List.cons.injEq] at arguments
  exact absurd arguments.1 (by simp)

/-- **Rigid view-colour heads are determined by the foreign canonical form.**
Two view-colour applications that are canonically equal at a foreign
declaration carry the same authored label and pointwise canonically equal
arguments. -/
theorem viewLabel_eq_of_foreign_canonical_eq
    {declarationColor viewColor : CostStaticColor}
    {leftLabel rightLabel : String}
    (leftRigid : (viewColor.symbols rhoCIGSLT).constructor leftLabel ≠
      (foreignDecl declarationColor).quoteConstructor)
    (rightRigid : (viewColor.symbols rhoCIGSLT).constructor rightLabel ≠
      (foreignDecl declarationColor).quoteConstructor)
    {leftArguments rightArguments : List Pattern}
    (equal : canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor leftLabel)
          leftArguments) =
      canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor rightLabel)
          rightArguments)) :
    leftLabel = rightLabel ∧
      leftArguments.map (canonicalize (foreignDecl declarationColor)) =
        rightArguments.map (canonicalize (foreignDecl declarationColor)) := by
  rw [canonicalize_apply_of_ne_quote _ leftRigid,
    canonicalize_apply_of_ne_quote _ rightRigid] at equal
  exact ⟨costStaticColor_constructor_inj (Pattern.apply.inj equal).1,
    (Pattern.apply.inj equal).2⟩

/-- **Collapse agreement for view-colour quote arguments.**  If one side's
quote argument is the view colour's drop wire and the other side's is any
rigid view-colour application, foreign canonical equality forces the second
to be the drop wire as well: the source canonicalizer's `Quote`/`Drop`
collapse therefore fires on both sides or on neither. -/
theorem collapseTrigger_agrees_of_foreign_canonical_eq
    {declarationColor viewColor : CostStaticColor}
    {rightLabel : String}
    (leftRigid : (viewColor.symbols rhoCIGSLT).constructor "PDrop" ≠
      (foreignDecl declarationColor).quoteConstructor)
    (rightRigid : (viewColor.symbols rhoCIGSLT).constructor rightLabel ≠
      (foreignDecl declarationColor).quoteConstructor)
    {leftArguments rightArguments : List Pattern}
    (equal : canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
          leftArguments) =
      canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor rightLabel)
          rightArguments)) :
    rightLabel = "PDrop" :=
  (viewLabel_eq_of_foreign_canonical_eq leftRigid rightRigid equal).1.symm

/-- **The residual differential configuration is canonically admissible.**
A foreign-colour `Quote`/`Drop` shell around a view-colour drop application
is canonically equal, at the foreign declaration, to that bare application.
The foreign canonicalizer therefore cannot separate a view-colour drop root
from a foreign-rooted subterm, and the collapse-agreement argument above does
not reach this configuration. -/
theorem foreignQuoteDropShell_canonical_eq_bare
    {declarationColor viewColor : CostStaticColor} (payload : Pattern) :
    canonicalize (foreignDecl declarationColor)
        (.apply ((declarationColor.symbols rhoCIGSLT).constructor "NQuote")
          [.apply ((declarationColor.symbols rhoCIGSLT).constructor "PDrop")
            [.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
              [payload]]]) =
      canonicalize (foreignDecl declarationColor)
        (.apply ((viewColor.symbols rhoCIGSLT).constructor "PDrop")
          [payload]) := by
  have quoteHead : (declarationColor.symbols rhoCIGSLT).constructor "NQuote" =
      (foreignDecl declarationColor).quoteConstructor :=
    (rhoDecl_quoteConstructor declarationColor).symm
  have dropHead : (declarationColor.symbols rhoCIGSLT).constructor "PDrop" =
      (foreignDecl declarationColor).dropConstructor :=
    (rhoDecl_dropConstructor declarationColor).symm
  rw [quoteHead, dropHead]
  exact canonicalize_quote_drop _ (declC_dropNeQuote declarationColor) _

/-- **An eligible stop never has a drop-headed root.**  Whenever a paired
plan stop classifies its left root as an application, that application is the
declaration's own quote; the eligibility table admits no other application
diagonal and no application/boundary mixture.  The `Quote`/`Drop` collapse of
the source canonicalizer is therefore never triggered by a stop leaf, on
either side, independently of any canonical equality. -/
theorem stopEligible_applicationRoot_eq_quote
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    {leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType}
    {rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPattern rightSourceType}
    (declaration : ReflectivePresentationDecl)
    (eligible : CostStaticPlanStopEligible declaration leftPlan rightPlan)
    {constructor : String}
    (leftApplication : leftPlan.rootClass = .application constructor) :
    constructor = declaration.quoteConstructor := by
  simp only [CostStaticPlanStopEligible, leftApplication] at eligible
  cases rightClass : rightPlan.rootClass <;> rw [rightClass] at eligible <;>
    first
      | exact eligible.1
      | exact eligible.elim

/-! ## Sort discipline at the collapse trigger -/

/-- The authored quote rule produces a name, never a process. -/
theorem rhoCalc_category_of_label_quote
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule)
    (membership : rule ∈ rhoCalc.terms)
    (label : rule.label = "NQuote") : rule.category = "Name" := by
  change rule ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd label (by decide)

/-- **A process-sorted plan is never quote-rooted.**  The source type of an
applied plan is the authored rule's result category, and the authored quote
rule produces a name. -/
theorem no_quoteApplicationRoot_of_processSourceType
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (processSort : sourceType = .base "Proc")
    (quoteRoot : plan.rootClass =
      .application rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor) :
    False := by
  cases plan with
  | application declared rendered current preimage notBare children =>
      rename_i wireName arguments
      have labelEq : preimage.sourceConstructor.1.label = "NQuote" :=
        CostStaticPlanRootClass.application.inj quoteRoot
      have categoryEq : preimage.sourceConstructor.1.category = "Name" :=
        rhoCalc_category_of_label_quote preimage.sourceConstructor.1
          preimage.sourceConstructor.2 labelEq
      rw [categoryEq] at processSort
      exact absurd processSort (by simp)
  | _ => simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- The abstract of a process-sorted plan that is not applied and not a
collection is a free variable. -/
theorem abstractPattern_shape_of_stopRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryRoot : plan.rootClass = .boundaryApplication ∨
      plan.rootClass = .boundaryCollection) :
    ∃ name, plan.abstractPattern = .fvar name := by
  cases plan with
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      exact ⟨_, rfl⟩
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact ⟨_, rfl⟩
  | _ =>
      rcases boundaryRoot with boundary | boundary <;>
        simp [CostStaticRegionPlan.rootClass] at boundary

/-- **The outer collapse trigger is never armed by a stop leaf.**  A
process-sorted plan admitted as one side of an eligible stop is a boundary or
a collection, so its reified abstract canonicalizes to a free variable or a
collection — never to a drop application.  The `Quote`/`Drop` collapse of the
source canonicalizer therefore cannot fire, and in particular cannot fire on
one side only. -/
theorem stopLeaf_abstract_not_dropApplication
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    {rightSourceBound rightTargetBound : List TypeExpr}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {rightAvailable : List TypeExpr}
    {rightOuter : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {rightPattern : Pattern} {rightSourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (partner : CostStaticRegionPlan rhoCIGSLT color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType)
    (processSort : sourceType = .base "Proc")
    (eligible : CostStaticPlanStopEligible
      rhoReflectivePresentation.toReflectivePresentationDecl plan partner)
    {arguments : List Pattern} :
    plan.abstractPattern ≠
      .apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
        arguments := by
  cases rootClass : plan.rootClass with
  | rigid =>
      simp only [CostStaticPlanStopEligible, rootClass] at eligible
  | application constructor =>
      exact absurd (rootClass.trans (congrArg CostStaticPlanRootClass.application
        (stopEligible_applicationRoot_eq_quote _ eligible rootClass)))
        (fun quoteRoot =>
          no_quoteApplicationRoot_of_processSourceType plan processSort quoteRoot)
  | boundaryApplication =>
      obtain ⟨name, shape⟩ := abstractPattern_shape_of_stopRoot plan (Or.inl rootClass)
      rw [shape]
      exact fun equal => Pattern.noConfusion equal
  | boundaryCollection =>
      obtain ⟨name, shape⟩ := abstractPattern_shape_of_stopRoot plan (Or.inr rootClass)
      rw [shape]
      exact fun equal => Pattern.noConfusion equal
  | collection collectionType =>
      cases plan with
      | collection choice selected children =>
          exact fun equal => Pattern.noConfusion equal
      | _ => simp [CostStaticRegionPlan.rootClass] at rootClass

/-- **A parallel-collection stop leaf can arm the outer collapse trigger.**
The parallel wrapper of a single drop application is canonically that drop
application, so the collection root class — unlike the boundary and applied
root classes — does not by itself keep the trigger disarmed.  Agreement across
the two sides must therefore be argued for collection stop leaves, not
inferred from the root classification. -/
theorem parallelSingleton_canonical_is_dropApplication
    (inner : Pattern) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (.collection
          rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          [.apply
            rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
            [inner]] none) =
      .apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
        [canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
          inner] := by
  rw [canonicalize_parallel_singleton,
    canonicalize_apply_of_ne_quote _ auth_dropNeQuote]
  simp only [List.map_cons, List.map_nil]

/-! ## The collection stop leaf -/

/-- No process plan is rooted at a boundary collection: the parallel
collection type is shared by both colours, so one colour can never reject a
collection the other selects. -/
theorem rho_no_boundaryCollectionRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryRoot : plan.rootClass = .boundaryCollection) : False := by
  cases plan with
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact rho_boundaryCollection_choices_absurd _ _ _ _ _ _ oppositeSelected
        currentRejected
  | _ => simp [CostStaticRegionPlan.rootClass] at boundaryRoot

/-- The view colour's parallel unit is rigid at any other colour's
declaration: a foreign canonicalizer retains it as an ordinary element
instead of erasing it. -/
theorem viewUnit_ne_foreignUnit {declarationColor viewColor : CostStaticColor}
    (different : declarationColor ≠ viewColor) :
    (viewColor.symbols rhoCIGSLT).constructor "PZero" ≠
      (foreignDecl declarationColor).parallelUnitConstructor := by
  rw [rhoDecl_unitConstructor]
  cases declarationColor <;> cases viewColor <;> first
    | exact absurd rfl different
    | decide

/-- **The unit-erasing witness fails the foreign alignment.**  A view-colour
parallel unit is erased by the authored canonicalizer but retained by a
foreign one, so a bare parallel and the same parallel extended by that unit —
the pair a unit-erasing collapse would need — are not foreign-canonically
equal.  The two payloads of a stop can therefore not differ by a current
colour unit. -/
theorem unitExtendedParallel_ne_bare_at_foreign
    {declarationColor viewColor : CostStaticColor}
    (different : declarationColor ≠ viewColor) :
    canonicalize (foreignDecl declarationColor)
        (.collection (foreignDecl declarationColor).parallelCollection
          [.bvar 0,
            .apply ((viewColor.symbols rhoCIGSLT).constructor "PZero") []]
          none) ≠
      canonicalize (foreignDecl declarationColor)
        (.collection (foreignDecl declarationColor).parallelCollection
          [.bvar 0] none) := by
  rw [canonicalize_parallel_singleton]
  set unitPattern : Pattern :=
    .apply ((viewColor.symbols rhoCIGSLT).constructor "PZero") [] with unitEq
  have unitNeQuote : (viewColor.symbols rhoCIGSLT).constructor "PZero" ≠
      (foreignDecl declarationColor).quoteConstructor := by
    rw [rhoDecl_quoteConstructor]
    cases declarationColor <;> cases viewColor <;> decide
  have unitCanonical : canonicalize (foreignDecl declarationColor)
      unitPattern = unitPattern := by
    rw [unitEq, canonicalize_apply_of_ne_quote _ unitNeQuote]
    rfl
  have keepsBoth : ∀ pattern ∈ [Pattern.bvar 0, unitPattern],
      pattern ≠ .apply (foreignDecl declarationColor).parallelUnitConstructor
        [] := by
    intro pattern membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact fun equal => Pattern.noConfusion equal
    · intro equal
      exact viewUnit_ne_foreignUnit different
        (Pattern.apply.inj (unitEq ▸ equal)).1
  simp only [canonicalize, beq_self_eq_true, if_true, canonicalizeList,
    canonicalize, unitCanonical, normalizeParallelElements, parallelSplice,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append]
  rw [List.filter_eq_self.2 (by
    intro pattern membership
    exact decide_eq_true (keepsBoth pattern membership))]
  have sortedLength : (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
      [Pattern.bvar 0, unitPattern]).length = 2 := by
    rw [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns, List.length_mergeSort]
    rfl
  obtain ⟨first, second, rest, shape⟩ :
      ∃ first second rest,
        Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          [Pattern.bvar 0, unitPattern] = first :: second :: rest := by
    match sorted : Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
        [Pattern.bvar 0, unitPattern], sortedLength with
    | first :: second :: rest, _ => exact ⟨first, second, rest, rfl⟩
  rw [shape]
  exact fun collapsed => Pattern.noConfusion collapsed

end QuoteDropCollapse
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
