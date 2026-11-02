import Mettapedia.Logic.HostingStyles.AmbientSpace.Atoms

/-!
# Located atoms: the run distributes over application and over the two binders

The candidate in which atoms reduce (`atomsReduce`) carries its space in a
run, and a run is one node: the run of an application is not the application
of two runs.  This module writes the presentation in which it is.

## The presentation

`located` has the sorts, the constructors and the sixteen rewrites of
`atomsReduce` (`located_terms`, `located_rewrites`), its equation of
quotation and dropping, and four more equations (`located_equations`):

| equation | left | right |
|---|---|---|
| `runApplicationEquation` | `run(space, App(F, X))` | `App(run(space, F), run(space, X))` |
| `runAbstractionEquation` | `run(space, Lam(A, x. B))` | `Lam(run(space, A), x. run(space, B))` |
| `runProductEquation` | `run(space, Pi(A, x. B))` | `Pi(run(space, A), x. run(space, B))` |
| `runRunEquation` | `run(outer, run(space, X))` | `run(space, X)` |

So a run distributes over application and over the two binders, and a run of
a run is the inner run.  An atom may then have its parts in different spaces:
the run is a constructor of atoms and is no longer bound to the root.

## What is proved here

* The presentation passes the declaration gate (`located_validate`).  The two
  equations with a binder are no equations between binder-free sides, so
  their rows are certified through the certificate of rewrites
  (`validateEquation_eq_nil_of_check`).
* The five laws on patterns (`Law`): each law is an equality of the static
  equivalence (`Law.equiv`), and every generator of the static equivalence is
  a law, read in one of its two directions (`located_generator`).
* The static equivalence of `atomsReduce` is contained in it
  (`atomsReduce_equiv_located`), and it is no longer that of quotation and
  dropping alone (`located_not_quoteDropOnly`).

## A remark on binders

An equation is instantiated by replacing its variables as they are written.
So the two equations with a binder move the space beneath the binder without
shifting it: for a space with no loose bound variable this is the intended
law, and every space of a closed term is such a space; a space that mentions
a bound variable is captured.  The module `NormalForm` gives the witness.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace (CarriesAtoms)

/-! ## The four equations of a run -/

/-- **The run of an application is the application of the runs.** -/
def runApplicationEquation : Equation :=
  { name := "prime-run-application"
    typeContext := []
    premises := []
    left := runPattern (.fvar "space") appLeft
    right := .apply "App"
      [runPattern (.fvar "space") (.fvar "F"), runPattern (.fvar "space") (.fvar "X")] }

/-- **The run of an abstraction is the abstraction of the runs.** -/
def runAbstractionEquation : Equation :=
  { name := "prime-run-abstraction"
    typeContext := []
    premises := []
    left := runPattern (.fvar "space") lamLeft
    right := .apply "Lam"
      [runPattern (.fvar "space") (.fvar "A"),
        .lambda none (runPattern (.fvar "space") (.fvar "B"))] }

/-- **The run of a product is the product of the runs.** -/
def runProductEquation : Equation :=
  { name := "prime-run-product"
    typeContext := []
    premises := []
    left := runPattern (.fvar "space") piLeft
    right := .apply "Pi"
      [runPattern (.fvar "space") (.fvar "A"),
        .lambda none (runPattern (.fvar "space") (.fvar "B"))] }

/-- **A run of a run is the inner run.** -/
def runRunEquation : Equation :=
  { name := "prime-run-run"
    typeContext := []
    premises := []
    left := runPattern (.fvar "outer") (runPattern (.fvar "space") (.fvar "X"))
    right := runPattern (.fvar "space") (.fvar "X") }

/-! ## The presentation -/

/-- **The candidate with located atoms**: the candidate in which atoms
reduce, with the four equations of a run. -/
def located : LanguageDef :=
  { atomsReduce with
    name := "metta-prime-located-atoms"
    equations :=
      [quoteDropEquation, runApplicationEquation, runAbstractionEquation, runProductEquation,
        runRunEquation] }

/-- **It extends the candidate in which atoms reduce**: the same sorts. -/
theorem located_types : located.types = atomsReduce.types := rfl

/-- The same constructors. -/
theorem located_terms : located.terms = atomsReduce.terms := rfl

/-- The same sixteen rewrites. -/
theorem located_rewrites : located.rewrites = atomsReduce.rewrites := rfl

/-- Its equation, and four more. -/
theorem located_equations :
    located.equations = atomsReduce.equations ++
      [runApplicationEquation, runAbstractionEquation, runProductEquation, runRunEquation] :=
  rfl

/-- The premises that it hands to an evaluator are those of the candidate in
which atoms reduce: no equation has a premise. -/
theorem located_premises : presentedPremises located = presentedPremises atomsReduce := rfl

/-! ## The declaration gate -/

/-- An equation, read as the rewrite from its left side to its right side. -/
def equationAsRewrite (equation : Equation) : RewriteRule :=
  { name := equation.name
    typeContext := equation.typeContext
    premises := equation.premises
    left := equation.left
    right := equation.right
    bindings := equation.bindings }

/-- The scope and naming conditions of a certified rule hold under every
message context.  This is `RewriteValidationCertificate.Certificate.patternsClean`
with the context a parameter: the row of an equation is reported under another
context than the row of a rewrite. -/
theorem rulePatterns_clean {language : LanguageDef} {rewrite : RewriteRule}
    (certificate : RewriteValidationCertificate.Certificate language rewrite) (context : String) :
    LanguageDef.validateRulePatterns context
      (RewriteValidationCertificate.constructorLabels language) rewrite.typeContext
      rewrite.premises rewrite.left rewrite.right = [] := by
  unfold LanguageDef.validateRulePatterns
  simp only [certificate.allPatternsScoped, if_true, List.append_eq_nil_iff, true_and]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.fvarsAvoidConstructors name membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.bindersAvoidConstructors name membership]
  · apply List.filterMap_eq_nil_iff.mpr
    intro entry membership
    simp [certificate.contextAvoidsConstructors entry membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    have bound := certificate.rightBound name membership
    simp only [List.mem_append] at bound
    rcases bound with leftBound | premiseBound
    · unfold LanguageDef.patternFvarNames at leftBound
      simp only [List.mem_filter] at leftBound
      simp [leftBound.1]
    · simp only [List.mem_flatMap] at premiseBound
      obtain ⟨premise, premiseMembership, nameMembership⟩ := premiseBound
      simp
      intro _ premiseAbsent
      exact (premiseAbsent premise premiseMembership nameMembership).elim

/-- **An equation whose rewrite passes the certificate of rewrites passes its
row of the declaration gate.**  The two rows run the same checks; the
certificate of rewrites covers sides with binders, which the test of
binder-free equations does not. -/
theorem validateEquation_eq_nil_of_check {language : LanguageDef} {equation : Equation}
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (checked : RewriteValidationCertificate.check language (equationAsRewrite equation) = true) :
    language.validateEquation equation = [] := by
  have certificate := RewriteValidationCertificate.certificate_of_check checked
  unfold LanguageDef.validateEquation
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · constructor
    · apply List.flatMap_eq_nil_iff.mpr
      intro entry entryMembership
      apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      exact certificate.contextTypes entry entryMembership
    · apply List.flatMap_eq_nil_iff.mpr
      intro type typeMembership
      apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      exact certificate.premiseTypes type typeMembership
  · exact RewriteValidationCertificate.validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ equation.left certificate.leftDeclared
  · exact RewriteValidationCertificate.validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ equation.right certificate.rightDeclared
  · apply List.flatMap_eq_nil_iff.mpr
    intro pattern patternMembership
    exact RewriteValidationCertificate.validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ pattern (certificate.premisesDeclared pattern patternMembership)
  · change LanguageDef.validateRulePatterns _
      (language.terms.map fun declaration => declaration.label) _ _ _ _ = []
    exact rulePatterns_clean certificate _

/-- The four equations of a run pass the certificate of rewrites. -/
theorem located_equations_checked :
    ∀ equation ∈
      [runApplicationEquation, runAbstractionEquation, runProductEquation, runRunEquation],
      RewriteValidationCertificate.check atomsReduce (equationAsRewrite equation) = true := by
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      atomsReduce_typeNames, atomsReduce_signatures, atomsReduce_labels,
      equationAsRewrite, runApplicationEquation, runAbstractionEquation, runProductEquation,
      runRunEquation, appLeft, piLeft, lamLeft, runPattern,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The candidate with located atoms passes the declaration gate.** -/
theorem located_validate : located.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hequations => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hequationValid =>
    intro equation member
    have listed : equation ∈
        [quoteDropEquation, runApplicationEquation, runAbstractionEquation, runProductEquation,
          runRunEquation] := member
    rcases List.mem_cons.mp listed with rfl | others
    · exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk (by decide +kernel)
    · exact validateEquation_eq_nil_of_check (language := located) (by decide +kernel)
        (located_equations_checked equation others)
  case hrewriteValid =>
    intro rewrite member
    exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check (language := located)
      (by decide +kernel) (atomsReduce_rewrites_checked rewrite member)

/-- The candidate with located atoms, as a presentation. -/
def locatedPresentation : ValidatedLanguageDef := ⟨located, located_validate⟩

/-! ## What it keeps of the candidate in which atoms reduce -/

/-- It carries the atoms of λΠ terms and the spaces of rules. -/
theorem located_carriesAtoms : CarriesAtoms located := by
  unfold CarriesAtoms
  decide

/-- Names are taken by dropping alone, as in the candidate in which atoms
reduce: the constructors are the same. -/
theorem located_namesOnlyDropped : NamesOnlyDropped located unquotedSorts :=
  atomsReduce_namesOnlyDropped

/-- Quotation takes an atom to a name and dropping takes a name. -/
theorem located_quoteDropSorted : QuoteDropSorted located := ⟨by decide, by decide⟩

/-- **Negative**: its static equivalence is not that of quotation and dropping
alone.  It has five equations. -/
theorem located_not_quoteDropOnly : ¬ QuoteDropOnly located := fun only =>
  absurd (congrArg List.length only.equations) (by decide)

/-! ## The five laws, on patterns -/

/-- **The five laws of the static equivalence**, on patterns, each written
from the side with the run outside.  The binder of an abstraction or of a
product carries a display name, which no law reads. -/
inductive Law : Pattern → Pattern → Prop where
  | quoteDrop (name : Pattern) : Law (quoted (dropped name)) name
  | application (space function argument : Pattern) :
      Law (runPattern space (.apply "App" [function, argument]))
        (.apply "App" [runPattern space function, runPattern space argument])
  | abstraction (space domain body : Pattern) (first second : Option String) :
      Law (runPattern space (.apply "Lam" [domain, .lambda first body]))
        (.apply "Lam" [runPattern space domain, .lambda second (runPattern space body)])
  | product (space domain body : Pattern) (first second : Option String) :
      Law (runPattern space (.apply "Pi" [domain, .lambda first body]))
        (.apply "Pi" [runPattern space domain, .lambda second (runPattern space body)])
  | inner (outer space subject : Pattern) :
      Law (runPattern outer (runPattern space subject)) (runPattern space subject)

variable {base : BasePremiseEvaluator}

/-- What matches the quotation of a dropping. -/
theorem mem_matchPattern_quotedDropped {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern quoteDropEquation.left pattern) :
    ∃ name, pattern = quoted (dropped name) ∧ bindings = [("name", name)] := by
  obtain ⟨inner, rfl, inInner⟩ := matched_apply_one (label := "prime-quote")
    (show bindings ∈ matchPattern (.apply "prime-quote" [.apply "prime-drop" [.fvar "name"]])
      pattern from matched)
  obtain ⟨name, rfl, inName⟩ := matched_apply_one (label := "prime-drop") inInner
  rw [mem_matchPattern_fvar] at inName
  exact ⟨name, rfl, inName⟩

/-- What matches a run of a run. -/
theorem mem_matchPattern_runRun {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern runRunEquation.left pattern) :
    ∃ outer space subject, pattern = runPattern outer (runPattern space subject) ∧
      bindings = [("space", space), ("X", subject), ("outer", outer)] := by
  obtain ⟨outer, inner, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run")
      (show bindings ∈ matchPattern
        (.apply "prime-run" [.fvar "outer", runPattern (.fvar "space") (.fvar "X")]) pattern from
        matched)
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide) inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨outer, space, subject, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- What matches two runs beneath a binary constructor, in one space: the
two spaces are one pattern. -/
theorem merged_runs {firstName secondName : String} (firstFresh : firstName ≠ "space")
    (secondFresh : secondName ≠ "space") (distinct : firstName ≠ secondName)
    {space other first second : Pattern} {bindings : Bindings}
    (merged : mergeBindings [(firstName, first), ("space", space)]
      [(secondName, second), ("space", other)] = some bindings) :
    space = other ∧ bindings = [(secondName, second), (firstName, first), ("space", space)] := by
  have firstMiss : (firstName == secondName) = false := by simpa using distinct
  have spaceMiss : ("space" == secondName) = false := by
    simpa using fun same : "space" = secondName => secondFresh same.symm
  have secondSpace : (secondName == "space") = false := by simpa using secondFresh
  have firstSpace : (firstName == "space") = false := by simpa using firstFresh
  by_cases same : space = other
  · subst same
    refine ⟨rfl, ?_⟩
    simpa [mergeBindings, firstMiss, spaceMiss, secondSpace, firstSpace] using merged.symm
  · exfalso
    simp [mergeBindings, firstMiss, spaceMiss, secondSpace, firstSpace, same] at merged

/-- **Every generator of the static equivalence is one of the five laws**,
read in one of its two directions. -/
theorem located_generator {source target : Pattern}
    (generator : EquationGenerator base located source target) :
    Law source target ∨ Law target source := by
  rcases generator with ⟨fuel, authored⟩ | derived
  swap
  · exact (no_derivedInstance_of_no_derived_laws (language := located) (by decide) (by decide)
      (by decide) _ _ derived).elim
  cases authored with
  | forward member _ matched premises applied =>
      rename_i equation initial final _
      have listed : equation ∈
          [quoteDropEquation, runApplicationEquation, runAbstractionEquation, runProductEquation,
            runRunEquation] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl | rfl | rfl
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨name, rfl, rfl⟩ := mem_matchPattern_quotedDropped matched
        have result : target = name := by
          rw [← applied]
          simp [quoteDropEquation, applyBindings]
        subst result
        exact .inl (.quoteDrop _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨space, function, argument, rfl, rfl⟩ := mem_matchPattern_runApp
          (show _ ∈ matchPattern (runPattern (.fvar "space") appLeft) source from matched)
        have result : target =
            .apply "App" [runPattern space function, runPattern space argument] := by
          rw [← applied]
          simp [runApplicationEquation, runPattern, applyBindings]
        subst result
        exact .inl (.application _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runLam
          (show _ ∈ matchPattern (runPattern (.fvar "space") lamLeft) source from matched)
        have result : target =
            .apply "Lam" [runPattern space domain, .lambda none (runPattern space body)] := by
          rw [← applied]
          simp [runAbstractionEquation, runPattern, applyBindings]
        subst result
        exact .inl (.abstraction _ _ _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runPi
          (show _ ∈ matchPattern (runPattern (.fvar "space") piLeft) source from matched)
        have result : target =
            .apply "Pi" [runPattern space domain, .lambda none (runPattern space body)] := by
          rw [← applied]
          simp [runProductEquation, runPattern, applyBindings]
        subst result
        exact .inl (.product _ _ _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨outer, space, subject, rfl, rfl⟩ := mem_matchPattern_runRun matched
        have result : target = runPattern space subject := by
          rw [← applied]
          simp [runRunEquation, runPattern, applyBindings]
        subst result
        exact .inl (.inner _ _ _)
  | reverse member _ matched premises applied =>
      rename_i equation initial final _
      have listed : equation ∈
          [quoteDropEquation, runApplicationEquation, runAbstractionEquation, runProductEquation,
            runRunEquation] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl | rfl | rfl
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        have bound : final = [("name", source)] := by
          simpa [quoteDropEquation, matchPattern] using matched
        subst bound
        have result : target = quoted (dropped source) := by
          rw [← applied]
          simp [quoteDropEquation, applyBindings, quoted, dropped]
        subst result
        exact .inr (.quoteDrop _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨left, right, first, second, rfl, inFirst, inSecond, merged⟩ :=
          matched_apply_two (label := "App")
            (show _ ∈ matchPattern (.apply "App"
              [runPattern (.fvar "space") (.fvar "F"), runPattern (.fvar "space") (.fvar "X")])
              source from matched)
        obtain ⟨space, function, rfl, rfl⟩ := mem_matchPattern_run (by decide) inFirst
        obtain ⟨other, argument, rfl, rfl⟩ := mem_matchPattern_run (by decide) inSecond
        obtain ⟨rfl, rfl⟩ := merged_runs (by decide) (by decide) (by decide) merged
        have result : target = runPattern space (.apply "App" [function, argument]) := by
          rw [← applied]
          simp [runApplicationEquation, runPattern, appLeft, applyBindings]
        subst result
        exact .inr (.application _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨left, right, first, second, rfl, inFirst, inSecond, merged⟩ :=
          matched_apply_two (label := "Lam")
            (show _ ∈ matchPattern (.apply "Lam"
              [runPattern (.fvar "space") (.fvar "A"),
                .lambda none (runPattern (.fvar "space") (.fvar "B"))]) source from matched)
        obtain ⟨space, domain, rfl, rfl⟩ := mem_matchPattern_run (by decide) inFirst
        obtain ⟨binder, inner, rfl, inInner⟩ := matched_lambda inSecond
        obtain ⟨other, body, rfl, rfl⟩ := mem_matchPattern_run (by decide) inInner
        obtain ⟨rfl, rfl⟩ := merged_runs (by decide) (by decide) (by decide) merged
        have result : target = runPattern space (.apply "Lam" [domain, .lambda none body]) := by
          rw [← applied]
          simp [runAbstractionEquation, runPattern, lamLeft, applyBindings]
        subst result
        exact .inr (.abstraction _ _ _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨left, right, first, second, rfl, inFirst, inSecond, merged⟩ :=
          matched_apply_two (label := "Pi")
            (show _ ∈ matchPattern (.apply "Pi"
              [runPattern (.fvar "space") (.fvar "A"),
                .lambda none (runPattern (.fvar "space") (.fvar "B"))]) source from matched)
        obtain ⟨space, domain, rfl, rfl⟩ := mem_matchPattern_run (by decide) inFirst
        obtain ⟨binder, inner, rfl, inInner⟩ := matched_lambda inSecond
        obtain ⟨other, body, rfl, rfl⟩ := mem_matchPattern_run (by decide) inInner
        obtain ⟨rfl, rfl⟩ := merged_runs (by decide) (by decide) (by decide) merged
        have result : target = runPattern space (.apply "Pi" [domain, .lambda none body]) := by
          rw [← applied]
          simp [runProductEquation, runPattern, piLeft, applyBindings]
        subst result
        exact .inr (.product _ _ _ _ _)
      · have same : final = initial := by
          change PremisesAt base located fuel initial [] final at premises
          cases premises
          rfl
        subst same
        obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide)
          (show _ ∈ matchPattern (runPattern (.fvar "space") (.fvar "X")) source from matched)
        have result : target = runPattern (.fvar "outer") (runPattern space subject) := by
          rw [← applied]
          simp [runRunEquation, runPattern, applyBindings]
        subst result
        exact .inr (.inner _ _ _)
  | @declared equation _ _ _ _ member notRaw _ =>
      have listed : equation ∈
          [quoteDropEquation, runApplicationEquation, runAbstractionEquation, runProductEquation,
            runRunEquation] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl | rfl | rfl <;> (rw [readsRaw_of_none rfl] at notRaw; cases notRaw)

/-! ## Each law is an equality of the static equivalence -/

/-- A quotation of a dropping and what was dropped: one instance of the
equation of quotation and dropping. -/
theorem quotedDropped_instance (name : Pattern) :
    EquationInstance base located (quoted (dropped name)) name :=
  ⟨0, .forward (equation := quoteDropEquation) (initialBindings := [("name", name)]) (.head _)
    (readsRaw_of_none rfl) (by simp [quoteDropEquation, quoted, dropped, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [quoteDropEquation, applyBindings])⟩

/-- **The run of an application and the application of the runs**: one
instance of the equation. -/
theorem runApplication_instance (space function argument : Pattern) :
    EquationInstance base located (runPattern space (.apply "App" [function, argument]))
      (.apply "App" [runPattern space function, runPattern space argument]) :=
  ⟨0, .forward (equation := runApplicationEquation)
    (initialBindings := [("F", function), ("X", argument), ("space", space)])
    (.tail _ (.head _))
    (readsRaw_of_none rfl) (by simp [runApplicationEquation, runPattern, appLeft, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runApplicationEquation, runPattern, applyBindings])⟩

/-- **The run of an abstraction and the abstraction of the runs**, the binder
of the result unnamed: one instance of the equation. -/
theorem runAbstraction_instance (space domain body : Pattern) (binder : Option String) :
    EquationInstance base located (runPattern space (.apply "Lam" [domain, .lambda binder body]))
      (.apply "Lam" [runPattern space domain, .lambda none (runPattern space body)]) :=
  ⟨0, .forward (equation := runAbstractionEquation)
    (initialBindings := [("A", domain), ("B", body), ("space", space)])
    (.tail _ (.tail _ (.head _)))
    (readsRaw_of_none rfl) (by simp [runAbstractionEquation, runPattern, lamLeft, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runAbstractionEquation, runPattern, applyBindings])⟩

/-- The abstraction of two runs in one space and the run of the abstraction,
whatever the display name of its binder: one instance of the equation, read
from its right side. -/
theorem runAbstraction_reverse (space domain body : Pattern) (binder : Option String) :
    EquationInstance base located
      (.apply "Lam" [runPattern space domain, .lambda binder (runPattern space body)])
      (runPattern space (.apply "Lam" [domain, .lambda none body])) :=
  ⟨0, .reverse (equation := runAbstractionEquation)
    (initialBindings := [("B", body), ("A", domain), ("space", space)])
    (.tail _ (.tail _ (.head _)))
    (readsRaw_of_none rfl) (by simp [runAbstractionEquation, runPattern, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runAbstractionEquation, runPattern, lamLeft, applyBindings])⟩

/-- **The run of a product and the product of the runs**, the binder of the
result unnamed: one instance of the equation. -/
theorem runProduct_instance (space domain body : Pattern) (binder : Option String) :
    EquationInstance base located (runPattern space (.apply "Pi" [domain, .lambda binder body]))
      (.apply "Pi" [runPattern space domain, .lambda none (runPattern space body)]) :=
  ⟨0, .forward (equation := runProductEquation)
    (initialBindings := [("A", domain), ("B", body), ("space", space)])
    (.tail _ (.tail _ (.tail _ (.head _))))
    (readsRaw_of_none rfl) (by simp [runProductEquation, runPattern, piLeft, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runProductEquation, runPattern, applyBindings])⟩

/-- The product of two runs in one space and the run of the product: one
instance of the equation, read from its right side. -/
theorem runProduct_reverse (space domain body : Pattern) (binder : Option String) :
    EquationInstance base located
      (.apply "Pi" [runPattern space domain, .lambda binder (runPattern space body)])
      (runPattern space (.apply "Pi" [domain, .lambda none body])) :=
  ⟨0, .reverse (equation := runProductEquation)
    (initialBindings := [("B", body), ("A", domain), ("space", space)])
    (.tail _ (.tail _ (.tail _ (.head _))))
    (readsRaw_of_none rfl) (by simp [runProductEquation, runPattern, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runProductEquation, runPattern, piLeft, applyBindings])⟩

/-- **A run of a run and the inner run**: one instance of the equation. -/
theorem runRun_instance (outer space subject : Pattern) :
    EquationInstance base located (runPattern outer (runPattern space subject))
      (runPattern space subject) :=
  ⟨0, .forward (equation := runRunEquation)
    (initialBindings := [("space", space), ("X", subject), ("outer", outer)])
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (readsRaw_of_none rfl) (by simp [runRunEquation, runPattern, matchPattern, matchArgs, mergeBindings])
    (.nil _) (by simp [runRunEquation, runPattern, applyBindings])⟩

/-- **Each law is an equality of the static equivalence.** -/
theorem Law.equiv {left right : Pattern} (law : Law left right) :
    EquationEquiv base located left right := by
  cases law with
  | quoteDrop name => exact equationInstance_equivalent (quotedDropped_instance _)
  | application space function argument =>
      exact equationInstance_equivalent (runApplication_instance space function argument)
  | abstraction space domain body first second =>
      exact .trans _ _ _
        (equationInstance_equivalent (runAbstraction_instance space domain body first))
        (.symm _ _ (.trans _ _ _
          (equationInstance_equivalent (runAbstraction_reverse space domain body second))
          (equationInstance_equivalent (runAbstraction_instance space domain body none))))
  | product space domain body first second =>
      exact .trans _ _ _
        (equationInstance_equivalent (runProduct_instance space domain body first))
        (.symm _ _ (.trans _ _ _
          (equationInstance_equivalent (runProduct_reverse space domain body second))
          (equationInstance_equivalent (runProduct_instance space domain body none))))
  | inner outer space subject =>
      exact equationInstance_equivalent (runRun_instance outer space subject)

/-- **The static equivalence of the candidate in which atoms reduce is
contained in that of the candidate with located atoms.** -/
theorem atomsReduce_equiv_located {first second : BasePremiseEvaluator} {left right : Pattern}
    (equivalent : EquationEquiv first atomsReduce left right) :
    EquationEquiv second located left right := by
  induction equivalent with
  | rel left right step =>
      cases step with
      | inContext context generator =>
          rcases atomsReduce_quoteDropOnly.generator generator with rfl | rfl
          · exact equationInstance_fill_equivalent context (quotedDropped_instance _)
          · exact .symm _ _ (equationInstance_fill_equivalent context (quotedDropped_instance _))
  | refl pattern => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ firstStep secondStep => exact .trans _ _ _ firstStep secondStep

#print axioms located_validate
#print axioms located_carriesAtoms
#print axioms located_namesOnlyDropped
#print axioms located_not_quoteDropOnly
#print axioms located_generator
#print axioms Law.equiv
#print axioms atomsReduce_equiv_located

end Mettapedia.Logic.HostingStyles.LocatedAtoms
