import Mettapedia.OSLF.MeTTaIL.CanonicalTyping
import Mathlib.Data.List.Sublists
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

/-!
# The reference relation modulo equations

A language's equations hold in every context and in both directions. The generators are:
- authored equation instances, scope-correct: an equation matches one side, its premises have
  witnesses, and the other side is instantiated with every value shifted from its capture depth
  (`AuthoredEquation`). An equation that declares the bound names its metavariables may use, and the
  arguments at each occurrence, is instantiated through that declaration instead: in any ambient
  scope the source is well scoped in, by the scoped matcher and instantiator
  (`ScopedEquationExecution.applyEquationAt`). So exchanging two binders swaps the body's arguments,
  and a component moved out of a binder may not use the bound name;
- the laws the presentation derives for its declared collections, exactly the canonical ones
  (`EquationSemantics.DerivedInstance`).

Closing the generators under one-hole contexts and under equivalence gives `Equivalent`. The reference
relation modulo equations takes one reference step between equivalent representatives (`StepModulo`).

On an aligned language whose equations are aligned (`EquationsAligned`: premises aligned, and no
metavariable deeper on the instantiated side than its capture depth), this is the canonical relation
modulo equations (`stepModuloEquations_iff`). On an equation-free language, equivalence is equality
(`equivalent_iff_eq_of_isEquationFree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (DerivedInstance StepModuloEquations EquationEquiv EquationContextStep EquationGenerator EquationInstance
    EquationInstanceAt)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- **An equation the ordinary matcher reads**: one declaring no binding dependencies, or one whose sides hold no
binder, where a declaration says nothing the matcher does not. -/
abbrev readsRaw (equation : Equation) : Bool := Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw equation

theorem readsRaw_of_none {equation : Equation} (undeclared : equation.bindings = none) : readsRaw equation = true :=
  Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none undeclared

open Mettapedia.OSLF.MeTTaIL.RuleBinding (admittedFor)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment matchRuleAt reduct?)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (closedRoot extendClosed)

/-- Where the premises of a declared equation bind: its captures are closed, so only the premises' own outputs. -/
def closedSites (premises : List Premise) : Pattern := captureSitesOf (.apply "" []) premises

/-- **A declared instance with premises**: the scoped matcher captures the source in the ambient scope, the premises
have witnesses over the closed captures, and the scoped instantiator emits the target. -/
def DeclaredPremised (equation : Equation) (orientation : Orientation) (ambient : ℕ) (witnesses : List Witness)
    (source target : Pattern) : Prop :=
  ∃ (spec : RuleBindingSpec) (captured : Assignment) (final : Bindings),
    (orientedRule equation orientation).bindings = some spec ∧
    admittedFor (orientedRule equation orientation) spec = true ∧
    source.isWellScopedAt ambient = true ∧
    captured ∈ matchRuleAt (orientedRule equation orientation) spec ambient source ∧
    PremisesValid relEnv language (closedSites equation.premises) (closedRoot captured) equation.premises witnesses
      final ∧
    reduct? (orientedRule equation orientation) spec ambient (extendClosed ambient captured final) = some target ∧
    target.isWellScopedAt ambient = true

/-- **An authored equation instance**: the equation matches the source by one side, its premises have
witnesses, and the target is the other side, instantiated scope-correctly. -/
inductive AuthoredEquation : Pattern → Pattern → Prop
  | forward {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations → readsRaw equation = true →
      initial ∈ matchPattern equation.left source →
      PremisesValid relEnv language (captureSitesOf equation.left equation.premises) initial equation.premises
        witnesses final →
      AuthoredEquation source (applyBindingsScoped (captureSitesOf equation.left equation.premises) final 0
        equation.right)
  | reverse {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations → readsRaw equation = true →
      initial ∈ matchPattern equation.right source →
      PremisesValid relEnv language (captureSitesOf equation.right equation.premises) initial equation.premises
        witnesses final →
      AuthoredEquation source (applyBindingsScoped (captureSitesOf equation.right equation.premises) final 0
        equation.left)
  /-- An equation with binders that declares its binding dependencies, in either orientation, at an ambient
  scope. -/
  | declared {equation : Equation} {orientation : ScopedEquationExecution.Orientation} {ambient : ℕ}
      {source target : Pattern} :
      equation ∈ language.equations → readsRaw equation = false →
      target ∈ ScopedEquationExecution.applyEquationAt language ambient equation orientation source →
      AuthoredEquation source target
  /-- A declared equation with premises, in either orientation, at an ambient scope: its premises have witnesses over
  the closed captures. -/
  | premised {equation : Equation} {orientation : Orientation} {ambient : ℕ} {witnesses : List Witness}
      {source target : Pattern} :
      equation ∈ language.equations → readsRaw equation = false → equation.premises ≠ [] →
      DeclaredPremised relEnv language equation orientation ambient witnesses source target →
      AuthoredEquation source target

/-- One generator of the equations: an authored instance or a derived collection law. -/
def Generator (source target : Pattern) : Prop :=
  AuthoredEquation relEnv language source target ∨ DerivedInstance language source target

/-- One generator in one context. -/
inductive EquationStep : Pattern → Pattern → Prop
  | inContext (context : OneHoleContext) {redex contractum : Pattern} :
      Generator relEnv language redex contractum →
      EquationStep (context.fill redex) (context.fill contractum)

/-- **Equivalence modulo the equations.** -/
def Equivalent : Pattern → Pattern → Prop :=
  Relation.EqvGen (EquationStep relEnv language)

/-- **The reference relation modulo equations**: one reference step between equivalent representatives. -/
def StepModulo (source target : Pattern) : Prop :=
  ∃ redex contractum, Equivalent relEnv language source redex ∧ Step relEnv language redex contractum ∧
    Equivalent relEnv language contractum target


/-- The existing presentation-derived equivalence, packaged as the authority for internal
boundaries. No new generators or equation meaning are introduced. -/
def equivalentSetoid : Setoid Pattern where
  r := Equivalent relEnv language
  iseqv := ⟨fun value => Relation.EqvGen.refl value,
    fun same => Relation.EqvGen.symm _ _ same,
    fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- The initial internal equation policy is selected only for languages whose authored equations
have no premises. Conditional equation evidence continues to use the literal reference family. -/
def UnconditionalEquations (selected : LanguageDef) : Prop :=
  ∀ equation ∈ selected.equations, equation.premises = []

/-- Select the actual source equivalence at internal provider and child boundaries. The guard
excludes recursive dependence through conditional equations; typing preservation is separate. -/
def declaredBoundaryPolicy (_ : UnconditionalEquations language) : InternalBoundaryPolicy :=
  .equational (equivalentSetoid relEnv language)

/-- Outer equation closure of the same reference family with an explicit internal policy. -/
def StepModuloWith (policy : InternalBoundaryPolicy) (source target : Pattern) : Prop :=
  ∃ redex contractum, Equivalent relEnv language source redex ∧
    StepWith policy relEnv language redex contractum ∧ Equivalent relEnv language contractum target

theorem stepModuloWith_presentation {source target : Pattern} :
    StepModuloWith relEnv language .presentation source target ↔ StepModulo relEnv language source target :=
  Iff.rfl

theorem stepModuloWith_equational_of_presentation (theory : Setoid Pattern) {source target : Pattern}
    (stepped : StepModulo relEnv language source target) :
    StepModuloWith relEnv language (.equational theory) source target := by
  obtain ⟨redex,contractum,before,step,after⟩ := stepped
  exact ⟨redex,contractum,before,stepWith_equational_of_presentation theory step,after⟩

/-! ## Aligned equations -/

/-- **An equation both relations interpret alike**: the ordinary matcher reads it, its premises are aligned from
either side, and neither side holds a metavariable deeper than where the other side captured
it. -/
def equationAligned (equation : Equation) : Bool :=
  readsRaw equation &&
  equation.premises.all (premiseAligned (captureSitesOf equation.left equation.premises)) &&
    equation.premises.all (premiseAligned (captureSitesOf equation.right equation.premises)) &&
    notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right &&
    notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left

/-- Every equation of the language is aligned. -/
def EquationsAligned : Prop := ∀ equation ∈ language.equations, equationAligned equation = true

/-! ## Agreement -/

variable {relEnv language}

theorem equationAligned_parts {equation : Equation} (aligned : equationAligned equation = true) :
    readsRaw equation = true ∧
    (∀ premise ∈ equation.premises, premiseAligned (captureSitesOf equation.left equation.premises) premise = true) ∧
      (∀ premise ∈ equation.premises, premiseAligned (captureSitesOf equation.right equation.premises) premise = true) ∧
      notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right = true ∧
      notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left = true := by
  simp only [equationAligned, Bool.and_eq_true, List.all_eq_true] at aligned
  exact ⟨aligned.1.1.1.1, aligned.1.1.1.2, aligned.1.1.2, aligned.1.2, aligned.2⟩

/-- **On aligned equations, the authored instances are the canonical ones.** -/
theorem authoredEquation_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationInstance (engineBasePremises relEnv) language source target ↔
      AuthoredEquation relEnv language source target := by
  constructor
  · rintro ⟨fuel, instanceEvidence⟩
    cases instanceEvidence with
    | @forward equation _ _ initial final member _ matched premises targetEq =>
      obtain ⟨undeclared, forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile forwardPremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.left equation.premises) final 0 equation.right forwardRight
      rw [← targetEq, ← instantiated]
      exact .forward member undeclared matched valid
    | @reverse equation _ _ initial final member _ matched premises targetEq =>
      obtain ⟨undeclared, -, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile reversePremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.right equation.premises) final 0 equation.left reverseLeft
      rw [← targetEq, ← instantiated]
      exact .reverse member undeclared matched valid
    | declared member notRaw _ => exact absurd (equationAligned_parts (equations _ member)).1 (by simp [notRaw])
  · intro authored
    cases authored with
    | @forward equation _ initial final witnesses member raw matched valid =>
      obtain ⟨-, forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses forwardPremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.right forwardRight]
      exact ⟨fuel, .forward member raw matched premises rfl⟩
    | @reverse equation _ initial final witnesses member raw matched valid =>
      obtain ⟨-, -, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses reversePremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.left reverseLeft]
      exact ⟨fuel, .reverse member raw matched premises rfl⟩
    | @declared equation _ _ _ _ member notRaw _ =>
      exact absurd (equationAligned_parts (equations equation member)).1 (by simp [notRaw])
    | @premised equation _ _ _ _ _ member notRaw _ _ =>
      exact absurd (equationAligned_parts (equations equation member)).1 (by simp [notRaw])

theorem generator_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationGenerator (engineBasePremises relEnv) language source target ↔ Generator relEnv language source target :=
  or_congr (authoredEquation_iff profile equations) Iff.rfl

theorem equationStep_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationContextStep (engineBasePremises relEnv) language source target ↔
      EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator => exact .inContext context ((generator_iff profile equations).mp generator)
  · intro step
    cases step with
    | inContext context generator => exact .inContext context ((generator_iff profile equations).mpr generator)

/-- **On aligned equations, equivalence is the canonical equivalence.** -/
theorem equivalent_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationEquiv (engineBasePremises relEnv) language source target ↔ Equivalent relEnv language source target :=
  ⟨fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff profile equations).mp step) _ _ equivalent,
    fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff profile equations).mpr step) _ _ equivalent⟩

/-- **On an aligned language with aligned equations, the reference relation modulo equations is the
canonical one.** -/
theorem stepModuloEquations_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    StepModuloEquations (engineBasePremises relEnv) language source target ↔
      StepModulo relEnv language source target := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff profile equations).mp before,
      (contextualStep_iff_step relEnv language profile).mp step, (equivalent_iff profile equations).mp after⟩
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff profile equations).mpr before,
      (contextualStep_iff_step relEnv language profile).mpr step, (equivalent_iff profile equations).mpr after⟩

/-! ## Equation-free languages -/

/-- **In an equation-free language, equivalence is equality**: it has no authored equations and no
collection laws. -/
theorem equivalent_iff_eq_of_isEquationFree (free : language.isEquationFree = true) {first second : Pattern} :
    Equivalent relEnv language first second ↔ first = second := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel _ _ step =>
      cases step with
      | inContext context generator =>
        rcases generator with authored | derived
        · cases authored <;>
            simp_all [Mettapedia.GSLT.LanguageDef.EquationSemantics.equations_eq_nil_of_isEquationFree free]
        · exact absurd derived
            (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_derivedInstance_of_isEquationFree free _ _)
    | refl => rfl
    | symm _ _ _ same => exact same.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- In an equation-free language, selecting the explicit internal equation policy retains the
literal witness, including the exact bindings and child/quantifier history. -/
theorem stepValid_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {source target : Pattern} (witness : Witness) :
    StepValid relEnv language source witness target (declaredBoundaryPolicy relEnv language unconditional) ↔
      StepValid relEnv language source witness target := by
  constructor
  · exact stepValid_presentation_of_equational
      (fun _ _ => equivalent_iff_eq_of_isEquationFree free) witness
  · exact stepValid_equational_of_presentation (equivalentSetoid relEnv language) witness

theorem premiseValid_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {sites : Pattern} {initial final : Bindings} {premise : Premise} (witness : Witness) :
    PremiseValid relEnv language sites initial premise witness final
        (declaredBoundaryPolicy relEnv language unconditional) ↔
      PremiseValid relEnv language sites initial premise witness final := by
  constructor
  · exact premiseValid_presentation_of_equational
      (fun _ _ => equivalent_iff_eq_of_isEquationFree free) witness
  · exact premiseValid_equational_of_presentation (equivalentSetoid relEnv language) witness

theorem premisesValid_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {sites : Pattern} {initial final : Bindings} {premises : List Premise} (witnesses : List Witness) :
    PremisesValid relEnv language sites initial premises witnesses final
        (declaredBoundaryPolicy relEnv language unconditional) ↔
      PremisesValid relEnv language sites initial premises witnesses final := by
  constructor
  · exact premisesValid_presentation_of_equational
      (fun _ _ => equivalent_iff_eq_of_isEquationFree free) witnesses
  · exact premisesValid_equational_of_presentation (equivalentSetoid relEnv language) witnesses

theorem forAllValid_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise} {elements : List Pattern}
    (witnesses : List Witness) :
    ForAllValid relEnv language sites bindings parameter body elements witnesses
        (declaredBoundaryPolicy relEnv language unconditional) ↔
      ForAllValid relEnv language sites bindings parameter body elements witnesses := by
  constructor
  · exact forAllValid_presentation_of_equational
      (fun _ _ => equivalent_iff_eq_of_isEquationFree free) witnesses
  · exact forAllValid_equational_of_presentation (equivalentSetoid relEnv language) witnesses

theorem stepWith_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {source target : Pattern} :
    StepWith (declaredBoundaryPolicy relEnv language unconditional) relEnv language source target ↔
      Step relEnv language source target :=
  stepWith_equational_iff_presentation (fun _ _ => equivalent_iff_eq_of_isEquationFree free)

theorem stepModuloWith_declared_iff_of_isEquationFree
    (unconditional : UnconditionalEquations language) (free : language.isEquationFree = true)
    {source target : Pattern} :
    StepModuloWith relEnv language (declaredBoundaryPolicy relEnv language unconditional) source target ↔
      Step relEnv language source target := by
  simp only [StepModuloWith,equivalent_iff_eq_of_isEquationFree free,
    stepWith_declared_iff_of_isEquationFree unconditional free]
  constructor
  · rintro ⟨redex,contractum,rfl,stepped,rfl⟩
    exact stepped
  · intro stepped
    exact ⟨source,target,rfl,stepped,rfl⟩

#print axioms stepModuloWith_presentation
#print axioms stepModuloWith_equational_of_presentation
#print axioms stepValid_declared_iff_of_isEquationFree
#print axioms premiseValid_declared_iff_of_isEquationFree
#print axioms premisesValid_declared_iff_of_isEquationFree
#print axioms forAllValid_declared_iff_of_isEquationFree
#print axioms stepWith_declared_iff_of_isEquationFree
#print axioms stepModuloWith_declared_iff_of_isEquationFree

/-! ## Intrinsic collection presentations and the actual source theory -/

/-- Without authored rows or algebra declarations, every actual source
generator is an intrinsic permutation or set-membership step. -/
theorem generator_bagStep (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) {source target : Pattern}
    (generator : Generator relEnv language source target) : CanonicalBags.BagStep source target := by
  rcases generator with authored | derived
  · cases authored with
    | forward member _ _ _ => rw [noEquations] at member; cases member
    | reverse member _ _ _ => rw [noEquations] at member; cases member
    | declared member _ _ => rw [noEquations] at member; cases member
    | premised member _ _ _ => rw [noEquations] at member; cases member
  · cases derived with
    | bagPerm _ _ permutation => exact .permute rfl permutation
    | setPerm _ _ permutation => exact .permute rfl permutation
    | setDedup _ _ => exact .members fun a => by simp
    | flatten declared _ _ =>
        exact (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_algebraRule_of_hasAlgebraDeclarations_eq_false
          noAlgebra declared).elim
    | singleton declared _ _ =>
        exact (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_algebraRule_of_hasAlgebraDeclarations_eq_false
          noAlgebra declared).elim
    | unitElim declared _ _ =>
        exact (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_algebraRule_of_hasAlgebraDeclarations_eq_false
          noAlgebra declared).elim
    | emptyUnit declared _ _ =>
        exact (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_algebraRule_of_hasAlgebraDeclarations_eq_false
          noAlgebra declared).elim

/-- Actual source equivalence implies intrinsic canonical equality under the
stated source-row/declaration hypotheses. No converse is assumed for an
undeclared collection occurrence. -/
theorem equivalent_same (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) {source target : Pattern}
    (related : Equivalent relEnv language source target) : CanonicalBags.Same source target := by
  induction related with
  | rel _ _ step =>
      cases step with
      | inContext context generator =>
          exact ((generator_bagStep noEquations noAlgebra generator).fill context).canon_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- The actual reference equivalence is closed under the existing structural
one-hole contexts; this grants no contextual rewrite permission. -/
theorem equivalent_fill (context : OneHoleContext) {source target : Pattern}
    (related : Equivalent relEnv language source target) :
    Equivalent relEnv language (context.fill source) (context.fill target) := by
  induction related with
  | rel _ _ step =>
      cases step with
      | inContext inner generator =>
          exact Relation.EqvGen.rel _ _ (by
            simpa only [OneHoleContext.fill_comp] using EquationStep.inContext (context.comp inner) generator)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

#print axioms generator_bagStep
#print axioms equivalent_same
#print axioms equivalent_fill

open Mettapedia.GSLT.LanguageDef.EquationSemantics (CollectionCarrierRule SortedAt)
open CanonicalBags (BagStep Same arrange)

/-- Evidence at one actual unordered collection occurrence. A vector uses no
collection equation. Each unordered node supplies an actual declared parameter
type occurrence and typing at its collection-data type. -/
def CollectionLawSite (language : LanguageDef) (kind : CollType) (values : List Pattern) : Prop :=
  kind = .vec ∨ ∃ rule,rule ∈ language.terms ∧
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind values

/-- A finite source-domain certificate for intrinsic collection equations.
Every rest-free unordered node has an actual declared collection-type occurrence. The
certificate recurses through the existing syntax, including nested collection
data and binder/substitution scopes; it does not imply whole-term typing. -/
inductive SourceCollections (language : LanguageDef) : Pattern → Prop where
  | bvar (index : Nat) : SourceCollections language (.bvar index)
  | fvar (key : String) : SourceCollections language (.fvar key)
  | apply {head : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments,SourceCollections language argument) →
      SourceCollections language (.apply head arguments)
  | lambda {display : Option String} {body : Pattern} :
      SourceCollections language body → SourceCollections language (.lambda display body)
  | multiLambda {arity : Nat} {display : List String} {body : Pattern} :
      SourceCollections language body → SourceCollections language (.multiLambda arity display body)
  | subst {body replacement : Pattern} :
      SourceCollections language body → SourceCollections language replacement →
      SourceCollections language (.subst body replacement)
  | collection {kind : CollType} {values : List Pattern} :
      CollectionLawSite language kind values → (∀ value ∈ values,SourceCollections language value) →
      SourceCollections language (.collection kind values none)

private theorem collectionTypedAt_bagStep {rule : GrammarRule} {kind : CollType}
    {first second : List Pattern}
    (step : BagStep (.collection kind first none) (.collection kind second none))
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind first) :
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind second := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,hasType⟩ := typed
  exact ⟨parameter,member,elementType,occurs,free,bound,step.hasType hasType⟩

private theorem collectionLawSite_bagStep {kind : CollType} {first second : List Pattern}
    (step : BagStep (.collection kind first none) (.collection kind second none))
    (site : CollectionLawSite language kind first) : CollectionLawSite language kind second := by
  rcases site with vector | ⟨rule,declared,typed⟩
  · exact Or.inl vector
  · exact Or.inr ⟨rule,declared,collectionTypedAt_bagStep step typed⟩

/-- Intrinsic rearrangement retains the actual declaration and data-type evidence
at each source occurrence. Repeated equal elements are not collapsed into an
assumed source matching witness. -/
theorem SourceCollections.of_bagStep {source target : Pattern} (step : BagStep source target) :
    SourceCollections language source → SourceCollections language target := by
  induction step with
  | permute unordered permutation =>
      intro good
      cases good with
      | collection site children =>
          exact .collection (collectionLawSite_bagStep (.permute unordered permutation) site)
            (fun value member => children value (permutation.mem_iff.mpr member))
  | members same =>
      intro good
      cases good with
      | collection site children =>
          exact .collection (collectionLawSite_bagStep (.members same) site)
            (fun value member => children value ((same value).mpr member))
  | apply inner ih =>
      intro good
      cases good with
      | apply children =>
          apply SourceCollections.apply
          intro value member
          simp only [List.mem_append,List.mem_cons] at member
          rcases member with before | rfl | after
          · exact children value (by simp [before])
          · exact ih (children _ (by simp))
          · exact children value (by simp [after])
  | lambda _ ih =>
      intro good
      cases good with
      | lambda body => exact .lambda (ih body)
  | multiLambda _ ih =>
      intro good
      cases good with
      | multiLambda body => exact .multiLambda (ih body)
  | substBody _ ih =>
      intro good
      cases good with
      | subst body replacement => exact .subst (ih body) replacement
  | substReplacement _ ih =>
      intro good
      cases good with
      | subst body replacement => exact .subst body (ih replacement)
  | element inner ih =>
      intro good
      cases good with
      | collection site children =>
          refine .collection (collectionLawSite_bagStep (.element inner) site) ?_
          intro value member
          simp only [List.mem_append,List.mem_cons] at member
          rcases member with before | rfl | after
          · exact children value (by simp [before])
          · exact ih (children _ (by simp))
          · exact children value (by simp [after])

/-- Eligibility is inherited by every intrinsically equal presentation, using
the independently proved intrinsic typing transport at each node. -/
theorem SourceCollections.of_same {source target : Pattern}
    (good : SourceCollections language source) (same : Same source target) : SourceCollections language target := by
  have chain := CanonicalBags.eqvGen_reflTransGen ((CanonicalBags.same_iff _ _).mp same)
  clear same
  induction chain with
  | refl => exact good
  | tail _ step ih => exact SourceCollections.of_bagStep step ih

private theorem intrinsic_source_law {source target : Pattern} (law : DerivedInstance language source target) :
    Equivalent relEnv language source target :=
  Relation.EqvGen.rel _ _ (.inContext .hole (.inr law))

/-- A declared typed set reaches its arranged presentation using actual
source permutations and adjacent duplicate elimination. -/
theorem set_arrange_equivalent {rule : GrammarRule}
    (declaration : rule ∈ language.terms) :
    ∀ (fuel : Nat) (values : List Pattern),values.length ≤ fuel →
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule .hashSet values →
    Equivalent relEnv language (.collection .hashSet values none)
      (.collection .hashSet (arrange .hashSet values) none)
  | fuel,values,short,sorted => by
      by_cases distinct : values.Nodup
      · have arranged : (arrange .hashSet values).Perm values := by
          show (PatternLexOrder.sortLex values).dedup.Perm values
          rw [List.Nodup.dedup ((PatternLexOrder.sortLex_perm values).nodup_iff.mpr distinct)]
          exact PatternLexOrder.sortLex_perm values
        exact intrinsic_source_law (.setPerm declaration sorted arranged.symm)
      · obtain ⟨duplicate,twice⟩ : ∃ duplicate,List.Sublist [duplicate,duplicate] values := by
          by_contra none
          exact distinct (List.nodup_iff_sublist.mpr fun value sub => none ⟨value,sub⟩)
        obtain ⟨others,permutation⟩ := twice.exists_perm_append
        have twiceSorted := collectionTypedAt_bagStep (.permute rfl permutation) sorted
        have onceSorted : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule .hashSet
            (duplicate::others) :=
          collectionTypedAt_bagStep (.members fun value => by simp) twiceSorted
        have toTwice := intrinsic_source_law (relEnv := relEnv) (.setPerm declaration sorted permutation)
        have toOnce := intrinsic_source_law (relEnv := relEnv) (.setDedup declaration twiceSorted)
        cases fuel with
        | zero =>
            have empty : values.length = 0 := by omega
            exact absurd (List.length_eq_zero_iff.mp empty ▸ List.nodup_nil) distinct
        | succ fuel =>
            have shorter : (duplicate::others).length ≤ fuel := by
              have lengths := permutation.length_eq
              simp only [List.length_append,List.length_cons,List.length_nil] at lengths
              simp only [List.length_cons]
              omega
            have rest := set_arrange_equivalent declaration fuel (duplicate::others) shorter onceSorted
            have same : arrange .hashSet (duplicate::others) = arrange .hashSet values := by
              apply CanonicalBags.arrange_eq_of_presents
              intro value
              rw [permutation.mem_iff]
              simp
            rw [same] at rest
            exact .trans _ _ _ toTwice (.trans _ _ _ toOnce rest)

/-- Extensional set presentations have actual source-equational witnesses
once its declaration and collection-data typing are supplied. -/
theorem set_members_equivalent {rule : GrammarRule} {first second : List Pattern}
    (declaration : rule ∈ language.terms)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule .hashSet first)
    (same : ∀ value,value ∈ first ↔ value ∈ second) :
    Equivalent relEnv language (.collection .hashSet first none) (.collection .hashSet second none) := by
  have secondSorted := collectionTypedAt_bagStep (.members same) sorted
  have toFirst := set_arrange_equivalent (relEnv := relEnv) declaration first.length first le_rfl sorted
  have toSecond := set_arrange_equivalent (relEnv := relEnv) declaration second.length second le_rfl secondSorted
  rw [CanonicalBags.arrange_eq_of_presents (kind := .hashSet) same] at toFirst
  exact .trans _ _ _ toFirst (.symm _ _ toSecond)

#print axioms SourceCollections.of_bagStep
#print axioms SourceCollections.of_same
#print axioms set_arrange_equivalent
#print axioms set_members_equivalent

/-- Each intrinsic step on an eligible source is realized by actual declared
source equations. The local declared-type certificate is consumed at its real
focus, before lifting through the structural context. -/
theorem bagStep_equivalent {source target : Pattern} (step : BagStep source target) :
    SourceCollections language source → Equivalent relEnv language source target := by
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
      intro good
      cases good with
      | collection site _ =>
          rcases site with vector | ⟨rule,declared,sorted⟩
          · subst kind
            cases unordered
          · cases kind with
            | vec => cases unordered
            | hashBag => exact intrinsic_source_law (.bagPerm declared sorted permutation)
            | hashSet => exact intrinsic_source_law (.setPerm declared sorted permutation)
  | members same =>
      intro good
      cases good with
      | collection site _ =>
          rcases site with impossible | ⟨rule,declared,sorted⟩
          · cases impossible
          · exact set_members_equivalent declared sorted same
  | @apply label before after argument changed inner ih =>
      intro good
      cases good with
      | apply children =>
          exact equivalent_fill (.apply label before .hole after) (ih (children _ (by simp)))
  | @lambda display body changed inner ih =>
      intro good
      cases good with
      | lambda bodyGood => exact equivalent_fill (.lambda display .hole) (ih bodyGood)
  | @multiLambda arity display body changed inner ih =>
      intro good
      cases good with
      | multiLambda bodyGood => exact equivalent_fill (.multiLambda arity display .hole) (ih bodyGood)
  | @substBody body changed replacement inner ih =>
      intro good
      cases good with
      | subst bodyGood _ => exact equivalent_fill (.substBody .hole replacement) (ih bodyGood)
  | @substReplacement body replacement changed inner ih =>
      intro good
      cases good with
      | subst _ replacementGood => exact equivalent_fill (.substReplacement body .hole) (ih replacementGood)
  | @element kind before after element changed rest inner ih =>
      intro good
      cases good with
      | collection _ children =>
          exact equivalent_fill (.collection kind before .hole after none) (ih (children _ (by simp)))

/-- Intrinsic equality earns an actual reference-equation witness when every
unordered source occurrence has its declaration and collection-data typing. -/
theorem equivalent_of_same {source target : Pattern} (good : SourceCollections language source)
    (same : Same source target) : Equivalent relEnv language source target := by
  have chain := CanonicalBags.eqvGen_reflTransGen ((CanonicalBags.same_iff _ _).mp same)
  clear same
  have lifted : SourceCollections language target ∧ Equivalent relEnv language source target := by
    induction chain with
    | refl => exact ⟨good,.refl _⟩
    | tail _ step ih =>
        exact ⟨SourceCollections.of_bagStep step ih.1,.trans _ _ _ ih.2 (bagStep_equivalent step ih.1)⟩
  exact lifted.2

/-- The actual source theory and intrinsic canonical equality agree on the
certified collection domain. The reverse direction is reconstructed from its
generators, not supplied as an eligibility field. -/
theorem equivalent_iff_same (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) {source target : Pattern}
    (good : SourceCollections language source) :
    Equivalent relEnv language source target ↔ Same source target :=
  ⟨equivalent_same noEquations noAlgebra,equivalent_of_same good⟩

#print axioms bagStep_equivalent
#print axioms equivalent_of_same
#print axioms equivalent_iff_same

/-- A wrapped-only collection inventory cannot sort a raw collection at any
base-result carrier, even when its metadata still mentions that kind. -/
theorem no_sorted_collection_of_no_bare_carriers
    (noBare : ∀ rule ∈ language.terms,CollectionLaws.bareKind rule = none)
    {kind : CollType} {values : List Pattern} {rest : Option String} {category : String} :
    ¬ SortedAt language (.collection kind values rest) category := by
  rintro ⟨free,bound,typed⟩
  cases typed with
  | collectionConstructor declared shape _ =>
      have missing := noBare _ declared
      simp only [CollectionLaws.bareKind,shape] at missing
      cases missing

#print axioms no_sorted_collection_of_no_bare_carriers

/-- Source intrinsic equations preserve the actual typed role and binder
scope of the endpoint. This uses the existing intrinsic typing theorem;
flattening and authored rows require separate certificates. -/
theorem equivalent_openPatternWellSorted
    (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (related : Equivalent relEnv language source target)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language free bound type source) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language free bound type target := by
  exact CanonicalBags.openPatternWellSorted_of_eqvGen
    ((CanonicalBags.same_iff source target).mp (equivalent_same noEquations noAlgebra related)) typed

#print axioms equivalent_openPatternWellSorted

/-- Adding declarations preserves the existing finite collection-type
eligibility evidence, including its original declaring rules. -/
theorem SourceCollections.of_terms_subset {first second : LanguageDef}
    (included : ∀ rule ∈ first.terms,rule ∈ second.terms) {pattern : Pattern}
    (good : SourceCollections first pattern) : SourceCollections second pattern := by
  induction good with
  | bvar index => exact .bvar index
  | fvar key => exact .fvar key
  | apply children ih => exact .apply ih
  | lambda body ih => exact .lambda ih
  | multiLambda body ih => exact .multiLambda ih
  | subst body replacement bodyIH replacementIH => exact .subst bodyIH replacementIH
  | collection site children ih =>
      refine .collection ?_ ih
      rcases site with vector | ⟨rule,member,typed⟩
      · exact Or.inl vector
      · exact Or.inr ⟨rule,included rule member,typed.of_terms_subset included⟩

/-- Intrinsic source equivalence on an eligible original term is conservative
under adding declarations. Authored equations and algebra remain outside this
certificate, so unrelated declarations cannot create new intrinsic equality. -/
theorem equivalent_iff_of_terms_subset {first second : LanguageDef}
    (included : ∀ rule ∈ first.terms,rule ∈ second.terms)
    (firstEquations : first.equations = [])
    (firstAlgebra : first.hasAlgebraDeclarations = false)
    (secondEquations : second.equations = [])
    (secondAlgebra : second.hasAlgebraDeclarations = false)
    {source target : Pattern} (good : SourceCollections first source) :
    Equivalent relEnv first source target ↔ Equivalent relEnv second source target := by
  rw [equivalent_iff_same firstEquations firstAlgebra good,
    equivalent_iff_same secondEquations secondAlgebra (good.of_terms_subset included)]

#print axioms SourceCollections.of_terms_subset
#print axioms equivalent_iff_of_terms_subset

/-! ## Unconditional authored rows -/

/-- Unconditional equations need no assumption about the language's directed
rules. Their source premise evidence is necessarily empty; the actual scope
checks still authorize readback from either equation side. -/
theorem authoredEquation_iff_unconditional (unconditional : UnconditionalEquations language)
    (equations : EquationsAligned language) {source target : Pattern} :
    EquationInstance (engineBasePremises relEnv) language source target ↔
      AuthoredEquation relEnv language source target := by
  constructor
  · rintro ⟨fuel,instanceEvidence⟩
    cases instanceEvidence with
    | @forward equation _ _ initial final member _ matched premises targetEq =>
        obtain ⟨undeclared, -, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
        obtain ⟨witnesses,valid⟩ : ∃ witnesses,PremisesValid relEnv language
            (captureSitesOf equation.left equation.premises) initial equation.premises witnesses final := by
          rw [unconditional equation member] at premises ⊢
          cases premises
          exact ⟨[],.nil _⟩
        have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
          (captureSitesOf equation.left equation.premises) final 0 equation.right forwardRight
        rw [← targetEq,← instantiated]
        exact .forward member undeclared matched valid
    | @reverse equation _ _ initial final member _ matched premises targetEq =>
        obtain ⟨undeclared, -, -, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
        obtain ⟨witnesses,valid⟩ : ∃ witnesses,PremisesValid relEnv language
            (captureSitesOf equation.right equation.premises) initial equation.premises witnesses final := by
          rw [unconditional equation member] at premises ⊢
          cases premises
          exact ⟨[],.nil _⟩
        have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
          (captureSitesOf equation.right equation.premises) final 0 equation.left reverseLeft
        rw [← targetEq,← instantiated]
        exact .reverse member undeclared matched valid
    | declared member notRaw _ => exact absurd (equationAligned_parts (equations _ member)).1 (by simp [notRaw])
  · intro authored
    cases authored with
    | @forward equation _ initial final witnesses member raw matched valid =>
        obtain ⟨-, -, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
        have premises : PremisesAt (engineBasePremises relEnv) language 0 initial equation.premises final := by
          rw [unconditional equation member] at valid ⊢
          cases valid
          exact .nil _
        rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.right forwardRight]
        exact ⟨0,.forward member raw matched premises rfl⟩
    | @reverse equation _ initial final witnesses member raw matched valid =>
        obtain ⟨-, -, -, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
        have premises : PremisesAt (engineBasePremises relEnv) language 0 initial equation.premises final := by
          rw [unconditional equation member] at valid ⊢
          cases valid
          exact .nil _
        rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.left reverseLeft]
        exact ⟨0,.reverse member raw matched premises rfl⟩
    | @declared equation _ _ _ _ member notRaw _ =>
        exact absurd (equationAligned_parts (equations equation member)).1 (by simp [notRaw])
    | @premised equation _ _ _ _ _ member notRaw _ _ =>
      exact absurd (equationAligned_parts (equations equation member)).1 (by simp [notRaw])

theorem generator_iff_unconditional (unconditional : UnconditionalEquations language)
    (equations : EquationsAligned language) {source target : Pattern} :
    EquationGenerator (engineBasePremises relEnv) language source target ↔ Generator relEnv language source target :=
  or_congr (authoredEquation_iff_unconditional unconditional equations) Iff.rfl

theorem equationStep_iff_unconditional (unconditional : UnconditionalEquations language)
    (equations : EquationsAligned language) {source target : Pattern} :
    EquationContextStep (engineBasePremises relEnv) language source target ↔
      EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator =>
        exact .inContext context ((generator_iff_unconditional unconditional equations).mp generator)
  · intro step
    cases step with
    | inContext context generator =>
        exact .inContext context ((generator_iff_unconditional unconditional equations).mpr generator)

/-- The original source-equivalence hub agrees with the actual equation
semantics on unconditional aligned rows, independently of directed rule
premise shapes and without changing any source generators. -/
theorem equivalent_iff_unconditional (unconditional : UnconditionalEquations language)
    (equations : EquationsAligned language) {source target : Pattern} :
    EquationEquiv (engineBasePremises relEnv) language source target ↔ Equivalent relEnv language source target :=
  ⟨fun related => Relation.EqvGen.mono
      (fun _ _ step => (equationStep_iff_unconditional unconditional equations).mp step) _ _ related,
    fun related => Relation.EqvGen.mono
      (fun _ _ step => (equationStep_iff_unconditional unconditional equations).mpr step) _ _ related⟩

#print axioms authoredEquation_iff_unconditional
#print axioms generator_iff_unconditional
#print axioms equationStep_iff_unconditional
#print axioms equivalent_iff_unconditional

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
