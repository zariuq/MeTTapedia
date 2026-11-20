import Mettapedia.OSLF.MeTTaIL.WrapperSites
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

/-!
# Firing at wrapper normal forms

A rule fires at wrapper normal forms when it has no premises, its left side never matches a wrapper
(`wrapperFree`), its right side is shaped for wrapper normal captures (`RightShaped`), its captures are
typed at types the wrapper laws keep (`CapturesTyped`), and its binder operation is ordinary
substitution or the presentation's reflective substitution (`WrapperFiringAdmissible`). The captures at
the normal form are the original captures mapped by their roles, and the reduct reaches the new reduct
by a forward chain of quote-drop and wrapper steps (`rootFiring_wrapper`). With sites that never pass
under a binder and an empty outer scope, every firing of a plan has a counterpart at the wrapper normal
form of its source (`primitive_wrapper`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralTypedSites ReflectiveSubstitution CanonicalBags CollectionLaws
open GeneralExecutionAdmission
open QuoteDrop (QuoteDropTyped)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

variable {laws : List Laws} {declaration : ReflectivePresentationDecl} {language : LanguageDef}
  {free : FreeTypeContext}

/-! ## Typed captures -/

variable (laws) in
/-- The type of a rest: one the wrapper laws keep, or a collection whose elements have such a type. -/
def RestTyped (type : TypeExpr) : Prop :=
  NoLawCollections laws type ∨ ∃ kind element, type = .collection kind element ∧ NoLawCollections laws element

/-- **The inner wrapper normal form keeps the type of a rest.** -/
theorem wrapperInner_hasType (admission : WrappersTyped laws language) {bound : List TypeExpr} {body : Pattern}
    {type : TypeExpr} (object : isObjectPattern body = true) (restOk : RestTyped laws type)
    (typed : HasType language free bound body type) : HasType language free bound (wrapperInner laws body) type := by
  cases body with
  | collection kind elements rest =>
    rw [wrapperInner_collection]
    have objects : isObjectPatternList elements = true := by
      simp only [isObjectPattern, Bool.and_eq_true] at object
      exact object.2
    rcases hasType_collection_inv typed with ⟨element, rfl, elementsTyped⟩ |
        ⟨rule, name, element, declared, parameters, rfl, elementsTyped⟩
    · have elementOk : NoLawCollections laws element := by
        rcases restOk with noLaw | ⟨kind', element', same, noLaw⟩
        · exact noLaw.2
        · cases same; exact noLaw
      exact .collection (elementsHaveType_wrapper admission elementOk objects elementsTyped)
    · exact .collectionConstructor declared parameters
        (elementsHaveType_wrapper admission (admission.bareElements rule declared name kind element
          ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2) objects
          elementsTyped)
  | bvar index => simpa [wrapperInner, wrapperNormal_bvar] using typed
  | fvar name => simpa [wrapperInner, wrapperNormal_fvar] using typed
  | subst body replacement => simp [isObjectPattern] at object
  | apply label arguments =>
    rcases restOk with noLaw | ⟨kind, element, rfl, _⟩
    · exact WrapperForward.hasType admission (to_wrapperNormal _) object noLaw typed
    · cases typed
  | lambda binder body =>
    rcases restOk with noLaw | ⟨kind, element, rfl, _⟩
    · exact WrapperForward.hasType admission (to_wrapperNormal _) object noLaw typed
    · cases typed
  | multiLambda arity binders body =>
    rcases restOk with noLaw | ⟨kind, element, rfl, _⟩
    · exact WrapperForward.hasType admission (to_wrapperNormal _) object noLaw typed
    · cases typed

variable (laws) in
/-- The rule's captures are typed at types the wrapper laws keep: an ordinary capture at a type without
collections of a flattening kind, a rest at a rest type. -/
def CapturesTyped (rests : List String) (rule : RewriteRule) : Prop :=
  ∀ name type, rule.typeContext.lookup name = some type →
    (name ∉ rests → NoLawCollections laws type) ∧ (name ∈ rests → RestTyped laws type)

theorem typedAssignment_wrapper {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    (admission : WrappersTyped laws environment.language) {rests : List String}
    (capturesTyped : CapturesTyped laws rests context.rule) {assignment : ScopedRuleMatching.Assignment}
    (typed : GeneralPremise.TypedAssignment environment context assignment) :
    GeneralPremise.TypedAssignment environment context (wrapperAssignment laws rests assignment) := by
  obtain ⟨sorts, objects⟩ := typed
  refine ⟨fun name value member => ?_, fun name value member => ?_⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, bodyTyped⟩ :=
      sorts name₀ value₀ inOriginal
    have object := objects name₀ value₀ inOriginal
    refine ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, ?_⟩
    obtain ⟨ordinaryOk, restOk⟩ := capturesTyped name₀ expected sort
    simp only [mapValue, captureMap]
    split
    · exact wrapperInner_hasType admission object (restOk ‹_›) bodyTyped
    · exact WrapperForward.hasType admission (to_wrapperNormal _) object (ordinaryOk ‹_›) bodyTyped
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    simp only [mapValue]
    exact WrapperForward.object (captureMap_forward rests name₀ value₀.body) (objects name₀ value₀ inOriginal)

/-! ## Root firings -/

variable (laws) in
/-- A rule fires at wrapper normal forms: no premises, a left side that never matches a wrapper, a right
side shaped for wrapper normal captures, captures typed at types the wrapper laws keep, and a binder
operation that is ordinary or the reflective substitution of a closed quote scope. -/
def WrapperFiringAdmissible (environment : GeneralPremise.Environment) (declaration : ReflectivePresentationDecl)
    (index : Nat) : Prop :=
  ∀ rule spec, environment.language.rewrites[index]? = some rule →
    GeneralPremise.specification? environment index = some spec →
    rule.premises = [] ∧ ∃ rests, wrapperFree laws rests rule.left = true ∧
      RightShaped declaration rule spec .right rests [] rule.right = true ∧ CapturesTyped laws rests rule ∧
      (substitutionPresentationForRule? environment.reflection rule = none ∨
        (substitutionPresentationForRule? environment.reflection rule = some declaration ∧
          declaration.quoteScope = .closed ∧ BinderWrapperCompatible laws declaration))

/-- **A root firing has a counterpart at the wrapper normal form of its focus**, with mapped captures and
a result reached by a forward chain, in an empty outer scope. -/
theorem rootFiring_wrapper {environment : GeneralPremise.Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (admission : WrappersTyped laws environment.language)
    (typedPresentation : QuoteDropTyped environment.language declaration)
    (unbound : bound = []) (noLaw : NoLawCollections laws type)
    (admissible : WrapperFiringAdmissible laws environment declaration index) :
    ∃ rests trace' target', GeneralPremise.RootFiring environment bound type (wrapperNormal laws source) index trace'
        (wrapperAssignment laws rests captured) (wrapperAssignment laws rests completed) history target' ∧
      QWForward laws declaration target target' := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified admitted sourceSorted matched typed premises reduced
      targetSorted =>
    obtain ⟨unconditional, rests, free, shaped, capturesTyped, selection⟩ := admissible rule spec selected specified
    rw [unconditional] at premises
    cases premises
    obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.traced_iff_matches.mpr
      (matches_wrapper (laws := laws) free (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩))
    subst unbound
    have closed : target.isWellScopedAt 0 = true := targetSorted.2.2.2
    unfold ScopedRuleMatching.reductWith? at reduced
    obtain ⟨target', reduced', forward⟩ := instantiateWith?_wrapper rule spec
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderRespectsWrapper_binderOperation distinct selection) rests rule.right .right [] captured target shaped
      reduced closed
    refine ⟨rests, trace', target', ?_, forward⟩
    refine .fire selected specified admitted
      (QWForward.openPatternWellSorted typedPresentation admission (QWForward.ofWrapper (to_wrapperNormal source)) noLaw
        sourceSorted) traced (typedAssignment_wrapper admission capturesTyped typed) ?_ reduced'
      (QWForward.openPatternWellSorted typedPresentation admission forward noLaw targetSorted)
    rw [unconditional]
    exact .nil

/-! ## Primitive firings -/

variable (laws) in
/-- Every rule of the plan fires at wrapper normal forms. -/
def RulesFireAtWrapper (plan : Plan) (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ rule ordinal, (rule, ordinal) ∈ plan.rules.zipIdx →
    WrapperFiringAdmissible laws (GeneralPlanEnvironment.environment plan) declaration ordinal

/-- Sites that never pass under a binder keep the outer scope. -/
theorem Licensed.focusBound_eq {permissions : OperationalPermissions} (noLambda : permissions.underLambda = false)
    (noMultiLambda : permissions.underMultiLambda = false) {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData} (licensed : Licensed language free permissions bound expected source site) :
    site.focusBound = bound := by
  induction licensed with
  | here => rfl
  | application _ _ _ _ _ _ _ _ _ ih => simpa [SiteData.wrapApplication] using ih
  | lambda enabled _ _ => rw [noLambda] at enabled; cases enabled
  | multiLambda enabled _ _ => rw [noMultiLambda] at enabled; cases enabled
  | directCollection _ _ _ _ _ ih => simpa [SiteData.wrapCollection] using ih
  | authoredCollection _ _ _ _ _ _ _ ih => simpa [SiteData.wrapCollection] using ih

/-- **Every firing has a counterpart at the wrapper normal form of its source**, with a result reached by
a forward chain, for sites that never pass under a binder in an empty outer scope. -/
theorem primitive_wrapper {plan : Plan} {expected : TypeExpr} {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (admission : WrappersTyped laws (GeneralPlanEnvironment.environment plan).language)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (noLambda : plan.permissions.sites.underLambda = false)
    (noMultiLambda : plan.permissions.sites.underMultiLambda = false)
    (expectedOk : NoLawCollections laws expected) (admissible : RulesFireAtWrapper laws plan declaration)
    (fired : GeneralOccurrenceSemantics.Primitive plan [] expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan [] expected (wrapperNormal laws source) receipt' ∧
      QWForward laws declaration receipt.target receipt'.target := by
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, sorted⟩ := fired
  obtain ⟨site', licensed', focus, focusBound, focusType, focusOk, fill, accepts'⟩ :=
    licensed_wrapper (declaration := declaration) admission licensed expectedOk
  have unbound : receipt.job.site.focusBound = [] := Licensed.focusBound_eq noLambda noMultiLambda licensed
  obtain ⟨rests, trace', localTarget', rooted', forwardLocal⟩ :=
    rootFiring_wrapper rooted distinct admission typedPresentation unbound focusOk (admissible _ _ declared)
  have forwardTarget : QWForward laws declaration receipt.target (site'.context.fill localTarget') := by
    rw [endpoint]; exact fill _ _ forwardLocal
  refine ⟨⟨⟨receipt.job.ordinal, receipt.job.declaration, site'⟩, trace', wrapperAssignment laws rests receipt.captured,
    wrapperAssignment laws rests receipt.completed, receipt.premiseHistory, localTarget', site'.context.fill localTarget'⟩,
    ⟨⟨declared, licensed'⟩, ?_, ?_, rfl, ?_⟩, forwardTarget⟩
  · simp only [focus, focusBound, focusType]
    exact rooted'
  · exact accepts' _ _ _ forwardLocal accepts
  · exact QWForward.openPatternWellSorted typedPresentation admission forwardTarget expectedOk sorted

end Mettapedia.OSLF.MeTTaIL.Wrappers
