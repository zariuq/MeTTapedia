import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# Declared equations, with and without premises, read alike by both relations

The reference relation and the canonical one agree on aligned equations that the ordinary matcher reads
(`authoredEquation_iff`). Equations that declare their binding dependencies are read by the scoped matcher in both:
- premise-free, through the same executor (`declaredInstanceAt_iff_applyEquationAt`);
- with premises, over the closed captures: witnesses on one side, derivations of bounded depth on the other.

So on a language whose raw equations are aligned and whose declared equations have premises aligned at the closed
captures (`EquationsReadAlike`), the authored instances are the canonical ones (`authoredEquation_iff_readAlike`), and
the reference relation modulo equations is the canonical one (`stepModuloEquations_iff_readAlike`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (DerivedInstance StepModuloEquations EquationEquiv EquationContextStep EquationGenerator EquationInstance
    EquationInstanceAt DeclaredInstanceAt declaredInstanceAt_iff_applyEquationAt
    declaredInstanceAt_of_applyEquationAt)

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- **An equation both relations read alike**: one the ordinary matcher reads, aligned; or a declared one, its
premises aligned at the closed captures. -/
def equationReadAlike (equation : Equation) : Bool :=
  if readsRaw equation then equationAligned equation
  else equation.premises.all (premiseAligned (closedSites equation.premises))

/-- Every equation of the language is read alike. -/
def EquationsReadAlike : Prop := ∀ equation ∈ language.equations, equationReadAlike equation = true

variable {relEnv language}

theorem EquationsReadAlike.raw (equations : EquationsReadAlike language) {equation : Equation}
    (member : equation ∈ language.equations) (raw : readsRaw equation = true) : equationAligned equation = true := by
  simpa [equationReadAlike, raw] using equations equation member

theorem EquationsReadAlike.declared (equations : EquationsReadAlike language) {equation : Equation}
    (member : equation ∈ language.equations) (notRaw : readsRaw equation = false) :
    ∀ premise ∈ equation.premises, premiseAligned (closedSites equation.premises) premise = true := by
  have read := equations equation member
  simp only [equationReadAlike, notRaw, Bool.false_eq_true, if_false, List.all_eq_true] at read
  exact read

/-- An aligned language whose equations are aligned reads them alike. -/
theorem EquationsReadAlike.of_aligned (equations : EquationsAligned language) : EquationsReadAlike language := by
  intro equation member
  have aligned := equations equation member
  have raw := (equationAligned_parts aligned).1
  simp [equationReadAlike, raw, aligned]

/-- **On equations read alike, the authored instances are the canonical ones**, declared equations with premises
included. -/
theorem authoredEquation_iff_readAlike (profile : ReferenceProfile language) (equations : EquationsReadAlike language)
    {source target : Pattern} :
    EquationInstance (engineBasePremises relEnv) language source target ↔
      AuthoredEquation relEnv language source target := by
  constructor
  · rintro ⟨fuel, instanceEvidence⟩
    cases instanceEvidence with
    | @forward equation _ _ initial final member raw matched premises targetEq =>
      obtain ⟨undeclared, forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations.raw member raw)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile forwardPremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.left equation.premises) final 0 equation.right forwardRight
      rw [← targetEq, ← instantiated]
      exact .forward member undeclared matched valid
    | @reverse equation _ _ initial final member raw matched premises targetEq =>
      obtain ⟨undeclared, -, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations.raw member raw)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile reversePremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.right equation.premises) final 0 equation.left reverseLeft
      rw [← targetEq, ← instantiated]
      exact .reverse member undeclared matched valid
    | @declared equation orientation ambient _ _ member notRaw declaredInstance =>
      by_cases premiseFree : equation.premises = []
      · exact .declared member notRaw ((declaredInstanceAt_iff_applyEquationAt premiseFree).mp declaredInstance)
      · obtain ⟨spec, captured, final, specified, admitted, sourceScoped, matched, premises, reduced, targetScoped⟩ :=
          declaredInstance
        obtain ⟨witnesses, valid⟩ :=
          premisesValid_of_premisesAt relEnv language profile (equations.declared member notRaw) premises
        exact .premised member notRaw premiseFree
          ⟨spec, captured, final, specified, admitted, sourceScoped, matched, valid, reduced, targetScoped⟩
  · intro authored
    cases authored with
    | @forward equation _ initial final witnesses member raw matched valid =>
      obtain ⟨-, forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations.raw member raw)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses forwardPremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.right forwardRight]
      exact ⟨fuel, .forward member raw matched premises rfl⟩
    | @reverse equation _ initial final witnesses member raw matched valid =>
      obtain ⟨-, -, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations.raw member raw)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses reversePremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.left reverseLeft]
      exact ⟨fuel, .reverse member raw matched premises rfl⟩
    | @declared equation orientation ambient _ _ member notRaw produced =>
      exact ⟨0, .declared member notRaw (declaredInstanceAt_of_applyEquationAt (fuel := 0) produced)⟩
    | @premised equation orientation ambient witnesses _ _ member notRaw _ declaredPremised =>
      obtain ⟨spec, captured, final, specified, admitted, sourceScoped, matched, valid, reduced, targetScoped⟩ :=
        declaredPremised
      obtain ⟨fuel, premises⟩ :=
        premisesAt_of_premisesValid relEnv language profile witnesses (equations.declared member notRaw) valid
      exact ⟨fuel, .declared member notRaw
        ⟨spec, captured, final, specified, admitted, sourceScoped, matched, premises, reduced, targetScoped⟩⟩

theorem generator_iff_readAlike (profile : ReferenceProfile language) (equations : EquationsReadAlike language)
    {source target : Pattern} :
    EquationGenerator (engineBasePremises relEnv) language source target ↔ Generator relEnv language source target :=
  or_congr (authoredEquation_iff_readAlike profile equations) Iff.rfl

theorem equationStep_iff_readAlike (profile : ReferenceProfile language) (equations : EquationsReadAlike language)
    {source target : Pattern} :
    EquationContextStep (engineBasePremises relEnv) language source target ↔
      EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context ((generator_iff_readAlike profile equations).mp generator)
  · intro step
    cases step with
    | inContext context generator =>
      exact .inContext context ((generator_iff_readAlike profile equations).mpr generator)

/-- **On equations read alike, equivalence is the canonical equivalence.** -/
theorem equivalent_iff_readAlike (profile : ReferenceProfile language) (equations : EquationsReadAlike language)
    {source target : Pattern} :
    EquationEquiv (engineBasePremises relEnv) language source target ↔ Equivalent relEnv language source target :=
  ⟨fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff_readAlike profile equations).mp step) _ _ equivalent,
    fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff_readAlike profile equations).mpr step) _ _ equivalent⟩

/-- **On an aligned language with equations read alike, the reference relation modulo equations is the canonical
one**, declared equations with premises included. -/
theorem stepModuloEquations_iff_readAlike (profile : ReferenceProfile language)
    (equations : EquationsReadAlike language) {source target : Pattern} :
    StepModuloEquations (engineBasePremises relEnv) language source target ↔
      StepModulo relEnv language source target := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff_readAlike profile equations).mp before,
      (contextualStep_iff_step relEnv language profile).mp step,
      (equivalent_iff_readAlike profile equations).mp after⟩
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff_readAlike profile equations).mpr before,
      (contextualStep_iff_step relEnv language profile).mpr step,
      (equivalent_iff_readAlike profile equations).mpr after⟩

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
