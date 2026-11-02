import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# Scoped steps within their source's scope are congruences

The core form of an authored congruence under a binder, `if x ~> y then (Lam ^z.x) ~> (Lam ^z.y)`, is a scoped step
premise with one local binder, whose source `x` the left side captures under one binder. The reference relation reads
a step premise through its endpoints and its step depth only (`stepEndpoints`, `stepDepth`), and the step depth is the
larger of the number of local binders and the source's capture depth. When the local binders fit within the capture
depth, the scoped step steps exactly as the congruence between the same endpoints.

- `fitsScope`, `flattenPremise`, `flattenRule`, `flattenScoped`: each scoped step premise that fits its source's scope
  written as a congruence.
- Each premise keeps its endpoints and its step depth (`stepDepth_flattenPremise`), so the rule keeps its binding sites
  (`captureSites_flattenRule`) and each premise holds alike (`premiseValid_flattenPremise_iff`).
- **The reference relation is unchanged**, witness for witness (`stepValid_flattenScoped_iff`,
  `step_flattenScoped_iff`); so are the instances of conditional equations, whose premises may step, under every
  reading of the equations (`readingStep_flattenScoped_iff`, `objectEquivalent_flattenScoped`); and with them the
  reading of the language through the reference relation (`referenceStructure_flattenScoped`,
  `sat_flattenScoped_iff`).

Strategies that read congruences between metavariables, the least contextual relation and finite-model certificates
among them, apply to the flattened language, and their answers are answers about the language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (captureDepth captureDepthList Bindings)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (EquationDiscipline DisciplinedStep DisciplinedEquation TypedStep
  AuthoredEquation EquationStep BindingsAdmitted Formed)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType HasSort FreeTypeContext CollectionTypedAt OpenPatternWellSorted)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance AlgebraRule SortedAt)

/-! ## Flattening -/

/-- **A scoped step premise fits its source's scope**: its source is a metavariable that the left side captures under
at least as many binders as the premise has local binders. -/
def fitsScope (left : Pattern) (premise : ScopedStepPremise) : Bool :=
  match premise.source with
  | .fvar name =>
    match captureDepth name 0 left with
    | some depth => decide (premise.binders.length ≤ depth)
    | none => false
  | _ => false

/-- A scoped step premise that fits its source's scope, as the congruence between its endpoints; any other premise as
it is. -/
def flattenPremise (left : Pattern) : Premise → Premise
  | .scopedStep premise => if fitsScope left premise then .congruence premise.source premise.target else .scopedStep premise
  | premise => premise

/-- A rule with its fitting scoped steps as congruences. -/
def flattenRule (rule : RewriteRule) : RewriteRule :=
  { rule with premises := rule.premises.map (flattenPremise rule.left) }

/-- **A language with its fitting scoped steps as congruences.** -/
def flattenScoped (language : LanguageDef) : LanguageDef :=
  { language with «rewrites» := language.rewrites.map flattenRule }

/-- A premise is unchanged by flattening, or it is a fitting scoped step and becomes its congruence. -/
theorem flattenPremise_cases (left : Pattern) (premise : Premise) :
    flattenPremise left premise = premise ∨
      ∃ inner, premise = .scopedStep inner ∧ fitsScope left inner = true ∧
        flattenPremise left premise = .congruence inner.source inner.target := by
  cases premise with
  | scopedStep inner =>
    by_cases fits : fitsScope left inner = true
    · exact .inr ⟨inner, rfl, fits, by simp only [flattenPremise, fits, if_true]⟩
    · exact .inl (by simp only [flattenPremise, fits, if_false, Bool.false_eq_true])
  | freshness _ | congruence _ _ | relationQuery _ _ | forAll _ _ _ => exact .inl rfl

/-! ## Endpoints, depths and sites -/

/-- **A fitting scoped step steps at its source's capture depth**, as its congruence does, wherever the left side
comes first among the binding sites. -/
theorem stepDepth_fits {left : Pattern} {inner : ScopedStepPremise} (fits : fitsScope left inner = true)
    (extra : List Pattern) :
    stepDepth (.apply "" (left :: extra)) (.congruence inner.source inner.target) =
      stepDepth (.apply "" (left :: extra)) (.scopedStep inner) := by
  unfold fitsScope at fits
  split at fits
  · rename_i name sourceEq
    split at fits
    · rename_i depth captured
      simp only [stepDepth, sourceEq, inPlaceDepth, captureDepth_sites, captured, Option.some_or, Option.getD_some]
      exact (Nat.max_eq_right (of_decide_eq_true fits)).symm
    · cases fits
  · cases fits

theorem stepDepth_flattenPremise (left : Pattern) (extra : List Pattern) (premise : Premise) :
    stepDepth (.apply "" (left :: extra)) (flattenPremise left premise) =
      stepDepth (.apply "" (left :: extra)) premise := by
  rcases flattenPremise_cases left premise with same | ⟨inner, rfl, fits, flat⟩
  · rw [same]
  · rw [flat]
    exact stepDepth_fits fits extra

theorem premiseSites_flattenPremise (left : Pattern) (extra : List Pattern) (premise : Premise) :
    premiseSites (left :: extra) (flattenPremise left premise) = premiseSites (left :: extra) premise := by
  rcases flattenPremise_cases left premise with same | ⟨inner, rfl, fits, flat⟩
  · rw [same]
  · rw [flat]
    simp only [premiseSites]
    rw [stepDepth_fits fits extra]

theorem foldl_flattenPremise (left : Pattern) :
    ∀ (premises : List Premise) (extra : List Pattern),
      (premises.map (flattenPremise left)).foldl (fun sites premise => sites ++ premiseSites sites premise)
          (left :: extra) =
        premises.foldl (fun sites premise => sites ++ premiseSites sites premise) (left :: extra)
  | [], _ => rfl
  | premise :: premises, extra => by
    simp only [List.map_cons, List.foldl_cons, premiseSites_flattenPremise left extra premise, List.cons_append]
    exact foldl_flattenPremise left premises (extra ++ premiseSites (left :: extra) premise)

/-- **Flattening keeps a rule's binding sites.** -/
theorem captureSites_flattenRule (rule : RewriteRule) : captureSites (flattenRule rule) = captureSites rule := by
  simp only [captureSites, captureSitesOf, flattenRule]
  rw [foldl_flattenPremise rule.left rule.premises []]

/-! ## Premises hold alike -/

variable (relEnv : RelationEnv)

/-- A fitting scoped step holds exactly where its congruence holds. -/
theorem premiseValid_fits_iff {language : LanguageDef} {left : Pattern} {extra : List Pattern}
    {inner : ScopedStepPremise} (fits : fitsScope left inner = true) {initial final : Bindings} {witness : Witness} :
    PremiseValid relEnv language (.apply "" (left :: extra)) initial (.congruence inner.source inner.target) witness
        final ↔
      PremiseValid relEnv language (.apply "" (left :: extra)) initial (.scopedStep inner) witness final := by
  have depth := stepDepth_fits fits extra
  constructor
  · intro valid
    cases valid with
    | base base _ => simp [isBase] at base
    | step endpoints stepped matched merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      rw [depth] at stepped
      exact .step rfl stepped matched merged
  · intro valid
    cases valid with
    | base base _ => simp [isBase] at base
    | step endpoints stepped matched merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      rw [← depth] at stepped
      exact .step rfl stepped matched merged

/-- **A premise holds alike flattened**, wherever the left side comes first among the binding sites. -/
theorem premiseValid_flattenPremise_iff {language : LanguageDef} {left : Pattern} {extra : List Pattern}
    {premise : Premise} {initial final : Bindings} {witness : Witness} :
    PremiseValid relEnv language (.apply "" (left :: extra)) initial (flattenPremise left premise) witness final ↔
      PremiseValid relEnv language (.apply "" (left :: extra)) initial premise witness final := by
  rcases flattenPremise_cases left premise with same | ⟨inner, rfl, fits, flat⟩
  · rw [same]
  · rw [flat]
    exact premiseValid_fits_iff relEnv fits

theorem premisesValid_flattenPremise_iff {language : LanguageDef} {left : Pattern} {extra : List Pattern} :
    ∀ {premises : List Premise} {witnesses : List Witness} {initial final : Bindings},
      PremisesValid relEnv language (.apply "" (left :: extra)) initial (premises.map (flattenPremise left)) witnesses
          final ↔
        PremisesValid relEnv language (.apply "" (left :: extra)) initial premises witnesses final
  | [], witnesses, initial, final => Iff.rfl
  | premise :: premises, witnesses, initial, final => by
    constructor
    · intro valid
      cases valid with
      | cons first rest =>
        exact .cons ((premiseValid_flattenPremise_iff relEnv).mp first) (premisesValid_flattenPremise_iff.mp rest)
    · intro valid
      cases valid with
      | cons first rest =>
        exact .cons ((premiseValid_flattenPremise_iff relEnv).mpr first) (premisesValid_flattenPremise_iff.mpr rest)

/-- Premises hold alike flattened, at a rule's binding sites. -/
theorem premisesValid_flattenRule_iff {language : LanguageDef} {rule : RewriteRule} {witnesses : List Witness}
    {initial final : Bindings} :
    PremisesValid relEnv language (captureSites (flattenRule rule)) initial (flattenRule rule).premises witnesses final ↔
      PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final := by
  rw [captureSites_flattenRule, captureSites_eq]
  exact premisesValid_flattenPremise_iff relEnv

theorem getElem?_flattenScoped (language : LanguageDef) (index : ℕ) :
    (flattenScoped language).rewrites[index]? = language.rewrites[index]?.map flattenRule := by
  simp only [flattenScoped, List.getElem?_map]

/-! ## The reference relation is unchanged -/

variable (language : LanguageDef)

mutual
/-- **A step of the language is a step of the flattened language**, with the same witness. -/
theorem stepValid_flatten : ∀ (witness : Witness) {source target : Pattern},
    StepValid relEnv language source witness target → StepValid relEnv (flattenScoped language) source witness target
  | .rule index _ witnesses, _, _, valid => by
    cases valid with
    | @rule _ _ rule _ _ _ found matched premises =>
      have found' : (flattenScoped language).rewrites[index]? = some (flattenRule rule) := by
        rw [getElem?_flattenScoped, found, Option.map_some]
      have flat := (premisesValid_flattenRule_iff relEnv (rule := rule)).mpr
        (premisesValid_flatten witnesses premises)
      have stepped := StepValid.rule found' (by simpa [flattenRule] using matched) flat
      rwa [captureSites_flattenRule] at stepped
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premisesValid_flatten : ∀ (witnesses : List Witness) {sites : Pattern} {initial final : Bindings}
    {premises : List Premise},
    PremisesValid relEnv language sites initial premises witnesses final →
      PremisesValid relEnv (flattenScoped language) sites initial premises witnesses final
  | [], _, _, _, _, valid => by
    cases valid
    exact .nil _
  | witness :: witnesses, _, _, _, _, valid => by
    cases valid with
    | cons first rest => exact .cons (premiseValid_flatten witness first) (premisesValid_flatten witnesses rest)

theorem premiseValid_flatten : ∀ (witness : Witness) {sites : Pattern} {initial final : Bindings} {premise : Premise},
    PremiseValid relEnv language sites initial premise witness final →
      PremiseValid relEnv (flattenScoped language) sites initial premise witness final
  | .base _, _, _, _, _, valid => by
    cases valid with
    | base base member => exact .base base member
  | .premiseStep step _ _ _, _, _, _, _, valid => by
    cases valid with
    | step endpoints stepped matched merged => exact .step endpoints (stepValid_flatten step stepped) matched merged
  | .forAll bodies, _, _, _, _, valid => by
    cases valid with
    | forAll lookup each => exact .forAll lookup (forAllValid_flatten bodies each)
  | .rule _ _ _, _, _, _, _, valid => by cases valid

theorem forAllValid_flatten : ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings} {parameter : String}
    {body : Premise} {elements : List Pattern},
    ForAllValid relEnv language sites bindings parameter body elements witnesses →
      ForAllValid relEnv (flattenScoped language) sites bindings parameter body elements witnesses
  | [], _, _, _, _, _, valid => by
    cases valid
    exact .nil
  | witness :: witnesses, _, _, _, _, _, valid => by
    cases valid with
    | cons first rest => exact .cons (premiseValid_flatten witness first) (forAllValid_flatten witnesses rest)
end

mutual
/-- **A step of the flattened language is a step of the language**, with the same witness. -/
theorem stepValid_unflatten : ∀ (witness : Witness) {source target : Pattern},
    StepValid relEnv (flattenScoped language) source witness target → StepValid relEnv language source witness target
  | .rule index _ witnesses, _, _, valid => by
    cases valid with
    | @rule _ _ flat _ _ _ found matched premises =>
      rw [getElem?_flattenScoped] at found
      obtain ⟨rule, original, rfl⟩ := Option.map_eq_some_iff.mp found
      have unflat := premisesValid_unflatten witnesses ((premisesValid_flattenRule_iff relEnv).mp premises)
      have stepped := StepValid.rule original (by simpa [flattenRule] using matched) unflat
      rwa [← captureSites_flattenRule] at stepped
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premisesValid_unflatten : ∀ (witnesses : List Witness) {sites : Pattern} {initial final : Bindings}
    {premises : List Premise},
    PremisesValid relEnv (flattenScoped language) sites initial premises witnesses final →
      PremisesValid relEnv language sites initial premises witnesses final
  | [], _, _, _, _, valid => by
    cases valid
    exact .nil _
  | witness :: witnesses, _, _, _, _, valid => by
    cases valid with
    | cons first rest => exact .cons (premiseValid_unflatten witness first) (premisesValid_unflatten witnesses rest)

theorem premiseValid_unflatten : ∀ (witness : Witness) {sites : Pattern} {initial final : Bindings} {premise : Premise},
    PremiseValid relEnv (flattenScoped language) sites initial premise witness final →
      PremiseValid relEnv language sites initial premise witness final
  | .base _, _, _, _, _, valid => by
    cases valid with
    | base base member => exact .base base member
  | .premiseStep step _ _ _, _, _, _, _, valid => by
    cases valid with
    | step endpoints stepped matched merged => exact .step endpoints (stepValid_unflatten step stepped) matched merged
  | .forAll bodies, _, _, _, _, valid => by
    cases valid with
    | forAll lookup each => exact .forAll lookup (forAllValid_unflatten bodies each)
  | .rule _ _ _, _, _, _, _, valid => by cases valid

theorem forAllValid_unflatten : ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise} {elements : List Pattern},
    ForAllValid relEnv (flattenScoped language) sites bindings parameter body elements witnesses →
      ForAllValid relEnv language sites bindings parameter body elements witnesses
  | [], _, _, _, _, _, valid => by
    cases valid
    exact .nil
  | witness :: witnesses, _, _, _, _, _, valid => by
    cases valid with
    | cons first rest => exact .cons (premiseValid_unflatten witness first) (forAllValid_unflatten witnesses rest)
end

/-- **Flattening keeps every witnessed step.** -/
theorem stepValid_flattenScoped_iff {source target : Pattern} {witness : Witness} :
    StepValid relEnv (flattenScoped language) source witness target ↔ StepValid relEnv language source witness target :=
  ⟨stepValid_unflatten relEnv language witness, stepValid_flatten relEnv language witness⟩

/-- **Flattening keeps the reference relation.** -/
theorem step_flattenScoped_iff {source target : Pattern} :
    Step relEnv (flattenScoped language) source target ↔ Step relEnv language source target :=
  exists_congr fun _ => stepValid_flattenScoped_iff relEnv language

/-! ## What flattening leaves alone: the constructors -/

theorem hasType_flattenScoped_iff {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} :
    HasType (flattenScoped language) free bound pattern type ↔ HasType language free bound pattern type :=
  ⟨HasType.of_terms_subset (source := flattenScoped language) (target := language) fun _ member => member,
    HasType.of_terms_subset (source := language) (target := flattenScoped language) fun _ member => member⟩

theorem sortedAt_flattenScoped_iff {pattern : Pattern} {category : String} :
    SortedAt (flattenScoped language) pattern category ↔ SortedAt language pattern category := by
  simp only [SortedAt, HasSort, hasType_flattenScoped_iff]

theorem algebraRule_flattenScoped_iff {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra} :
    AlgebraRule (flattenScoped language) rule kind algebra ↔ AlgebraRule language rule kind algebra :=
  ⟨fun declared => ⟨declared.authored, declared.declared, declared.selfSorted, declared.unitAuthored⟩,
    fun declared => ⟨declared.authored, declared.declared, declared.selfSorted, declared.unitAuthored⟩⟩

/-- **The collection laws are the same** in the flattened language. -/
theorem derivedInstance_flattenScoped_iff {source target : Pattern} :
    DerivedInstance (flattenScoped language) source target ↔ DerivedInstance language source target := by
  constructor
  · intro law
    cases law with
    | bagPerm member typed perm => exact .bagPerm member (CollectionTypedAt.of_terms_subset (source := flattenScoped language) (target := language)
        (fun _ member => member) typed) perm
    | setPerm member typed perm => exact .setPerm member (CollectionTypedAt.of_terms_subset (source := flattenScoped language) (target := language)
        (fun _ member => member) typed) perm
    | setDedup member typed => exact .setDedup member (CollectionTypedAt.of_terms_subset (source := flattenScoped language) (target := language)
        (fun _ member => member) typed)
    | flatten declared flattens sorted =>
      exact .flatten ((algebraRule_flattenScoped_iff language).mp declared) flattens
        ((sortedAt_flattenScoped_iff language).mp sorted)
    | singleton declared flattens sorted =>
      exact .singleton ((algebraRule_flattenScoped_iff language).mp declared) flattens
        ((sortedAt_flattenScoped_iff language).mp sorted)
    | unitElim declared unit sorted =>
      exact .unitElim ((algebraRule_flattenScoped_iff language).mp declared) unit
        ((sortedAt_flattenScoped_iff language).mp sorted)
    | emptyUnit declared unit sorted =>
      exact .emptyUnit ((algebraRule_flattenScoped_iff language).mp declared) unit
        ((sortedAt_flattenScoped_iff language).mp sorted)
  · intro law
    cases law with
    | bagPerm member typed perm => exact .bagPerm member (CollectionTypedAt.of_terms_subset (source := language) (target := flattenScoped language)
        (fun _ member => member) typed) perm
    | setPerm member typed perm => exact .setPerm member (CollectionTypedAt.of_terms_subset (source := language) (target := flattenScoped language)
        (fun _ member => member) typed) perm
    | setDedup member typed => exact .setDedup member (CollectionTypedAt.of_terms_subset (source := language) (target := flattenScoped language)
        (fun _ member => member) typed)
    | flatten declared flattens sorted =>
      exact .flatten ((algebraRule_flattenScoped_iff language).mpr declared) flattens
        ((sortedAt_flattenScoped_iff language).mpr sorted)
    | singleton declared flattens sorted =>
      exact .singleton ((algebraRule_flattenScoped_iff language).mpr declared) flattens
        ((sortedAt_flattenScoped_iff language).mpr sorted)
    | unitElim declared unit sorted =>
      exact .unitElim ((algebraRule_flattenScoped_iff language).mpr declared) unit
        ((sortedAt_flattenScoped_iff language).mpr sorted)
    | emptyUnit declared unit sorted =>
      exact .emptyUnit ((algebraRule_flattenScoped_iff language).mpr declared) unit
        ((sortedAt_flattenScoped_iff language).mpr sorted)

theorem bindingsAdmitted_flattenScoped_iff {discipline : EquationDiscipline} {typeContext : List (String × TypeExpr)}
    {bindings : Bindings} :
    BindingsAdmitted (flattenScoped language) discipline typeContext bindings ↔
      BindingsAdmitted language discipline typeContext bindings := by
  cases discipline <;> simp only [BindingsAdmitted, hasType_flattenScoped_iff]

theorem formed_flattenScoped_iff {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {formed : Pattern → Prop} {term : Pattern} :
    Formed (flattenScoped language) free bound type formed term ↔ Formed language free bound type formed term :=
  ⟨fun term => ⟨term.object, (hasType_flattenScoped_iff language).mp term.typed, term.formed⟩,
    fun term => ⟨term.object, (hasType_flattenScoped_iff language).mpr term.typed, term.formed⟩⟩

/-! ## Equations hold alike -/

/-- Premises hold alike in the flattened language. -/
theorem premisesValid_flattenScoped_iff {sites : Pattern} {initial final : Bindings} {premises : List Premise}
    {witnesses : List Witness} :
    PremisesValid relEnv (flattenScoped language) sites initial premises witnesses final ↔
      PremisesValid relEnv language sites initial premises witnesses final :=
  ⟨premisesValid_unflatten relEnv language witnesses, premisesValid_flatten relEnv language witnesses⟩

theorem declaredPremised_flattenScoped_iff {equation : Equation}
    {orientation : Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.Orientation} {ambient : Nat}
    {witnesses : List Witness} {source target : Pattern} :
    DeclaredPremised relEnv (flattenScoped language) equation orientation ambient witnesses source target ↔
      DeclaredPremised relEnv language equation orientation ambient witnesses source target := by
  constructor
  · rintro ⟨spec, captured, final, specified, admitted, sourceScoped, matched, valid, reduced, targetScoped⟩
    exact ⟨spec, captured, final, specified, admitted, sourceScoped, matched,
      (premisesValid_flattenScoped_iff relEnv language).mp valid, reduced, targetScoped⟩
  · rintro ⟨spec, captured, final, specified, admitted, sourceScoped, matched, valid, reduced, targetScoped⟩
    exact ⟨spec, captured, final, specified, admitted, sourceScoped, matched,
      (premisesValid_flattenScoped_iff relEnv language).mpr valid, reduced, targetScoped⟩

/-- **An authored equation instance is one in the flattened language**: its premises hold alike. -/
theorem authoredEquation_flattenScoped_iff {source target : Pattern} :
    AuthoredEquation relEnv (flattenScoped language) source target ↔ AuthoredEquation relEnv language source target := by
  constructor
  · intro instance_
    cases instance_ with
    | forward member undeclared matched premises =>
      exact .forward member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mp premises)
    | reverse member undeclared matched premises =>
      exact .reverse member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mp premises)
    | declared member notRaw produced =>
      exact .declared member notRaw (Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.applyEquationAt_language _ language _ _ _ _ ▸ produced)
    | premised member notRaw premised declaredPremised =>
      exact .premised member notRaw premised ((declaredPremised_flattenScoped_iff relEnv language).mp declaredPremised)
  · intro instance_
    cases instance_ with
    | forward member undeclared matched premises =>
      exact .forward member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mpr premises)
    | reverse member undeclared matched premises =>
      exact .reverse member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mpr premises)
    | declared member notRaw produced =>
      exact .declared member notRaw (Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.applyEquationAt_language language _ _ _ _ _ ▸ produced)
    | premised member notRaw premised declaredPremised =>
      exact .premised member notRaw premised ((declaredPremised_flattenScoped_iff relEnv language).mpr declaredPremised)

theorem equationStep_flattenScoped_iff {source target : Pattern} :
    EquationStep relEnv (flattenScoped language) source target ↔ EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp (authoredEquation_flattenScoped_iff relEnv language).mp
        (derivedInstance_flattenScoped_iff language).mp)
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp (authoredEquation_flattenScoped_iff relEnv language).mpr
        (derivedInstance_flattenScoped_iff language).mpr)

theorem disciplinedEquation_flattenScoped_iff {discipline : EquationDiscipline} {source target : Pattern} :
    DisciplinedEquation relEnv (flattenScoped language) discipline source target ↔
      DisciplinedEquation relEnv language discipline source target := by
  constructor
  · intro instance_
    cases instance_ with
    | forward member undeclared matched premises admitted scope =>
      exact .forward member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mp premises)
        ((bindingsAdmitted_flattenScoped_iff language).mp admitted) scope
    | reverse member undeclared matched premises admitted scope =>
      exact .reverse member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mp premises)
        ((bindingsAdmitted_flattenScoped_iff language).mp admitted) scope
    | declared raw member notRaw produced =>
      exact .declared raw member notRaw (Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.applyEquationAt_language _ language _ _ _ _ ▸ produced)
    | premised raw member notRaw premised declaredPremised =>
      exact .premised raw member notRaw premised ((declaredPremised_flattenScoped_iff relEnv language).mp declaredPremised)
  · intro instance_
    cases instance_ with
    | forward member undeclared matched premises admitted scope =>
      exact .forward member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mpr premises)
        ((bindingsAdmitted_flattenScoped_iff language).mpr admitted) scope
    | reverse member undeclared matched premises admitted scope =>
      exact .reverse member undeclared matched ((premisesValid_flattenScoped_iff relEnv language).mpr premises)
        ((bindingsAdmitted_flattenScoped_iff language).mpr admitted) scope
    | declared raw member notRaw produced =>
      exact .declared raw member notRaw (Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution.applyEquationAt_language language _ _ _ _ _ ▸ produced)
    | premised raw member notRaw premised declaredPremised =>
      exact .premised raw member notRaw premised ((declaredPremised_flattenScoped_iff relEnv language).mpr declaredPremised)

theorem disciplinedStep_flattenScoped_iff {discipline : EquationDiscipline} {source target : Pattern} :
    DisciplinedStep relEnv (flattenScoped language) discipline source target ↔
      DisciplinedStep relEnv language discipline source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp (disciplinedEquation_flattenScoped_iff relEnv language).mp
        (derivedInstance_flattenScoped_iff language).mp)
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context (generator.imp (disciplinedEquation_flattenScoped_iff relEnv language).mpr
        (derivedInstance_flattenScoped_iff language).mpr)

/-- **Each reading of the equations steps alike** in the flattened language. -/
theorem readingStep_flattenScoped_iff (equations : EquationReading) {source target : Pattern} :
    readingStep relEnv (flattenScoped language) equations source target ↔
      readingStep relEnv language equations source target := by
  match equations with
  | .instances .raw => exact equationStep_flattenScoped_iff relEnv language
  | .instances .sorted => exact disciplinedStep_flattenScoped_iff relEnv language
  | .instances .fresh => exact disciplinedStep_flattenScoped_iff relEnv language
  | .instances .closed => exact disciplinedStep_flattenScoped_iff relEnv language
  | .typed discipline profile types names =>
    simp only [readingStep, TypedStep, formed_flattenScoped_iff, disciplinedStep_flattenScoped_iff]
    rfl

/-- **Object terms are equivalent alike** in the flattened language. -/
theorem objectEquivalent_flattenScoped (reading : LanguageReading) :
    ObjectEquivalent relEnv (flattenScoped language) reading = ObjectEquivalent relEnv language reading := by
  unfold ObjectEquivalent
  congr 1
  funext first second
  simp only [ObjectStep, readingStep_flattenScoped_iff]

/-- **The reading through the reference relation is unchanged**: the flattened language has the same native
structure. -/
theorem referenceStructure_flattenScoped (reading : LanguageReading) (reference : reading.rules = .reference) :
    referenceStructure relEnv (flattenScoped language) reading = referenceStructure relEnv language reading := by
  obtain ⟨equations, rules⟩ := reading
  subst reference
  unfold referenceStructure
  rw [placed_eq_of_objectEquivalent_eq (objectEquivalent_flattenScoped (relEnv := relEnv) (language := language) _)]
  simp only [objectEquivalent_flattenScoped, RuleValid, stepValid_flattenScoped_iff]
  congr 1
  funext element type
  simp only [carrierTyped_congr (language := flattenScoped language) (other := language) rfl rfl]

/-- **Native types are unchanged by flattening**, in a reading through the reference relation. -/
theorem sat_flattenScoped_iff (reading : LanguageReading) (reference : reading.rules = .reference) {n : ℕ}
    (env : Env Pattern n) (formula : Formula n) (term : Pattern) :
    (referenceStructure relEnv (flattenScoped language) reading).sat env formula term ↔
      (referenceStructure relEnv language reading).sat env formula term := by
  rw [referenceStructure_flattenScoped relEnv language reading reference]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
