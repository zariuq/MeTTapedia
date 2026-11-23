import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedContainment

/-!
# Every root step headed: a run is the member at its space, at every ambient space

`headedContained` heads the ambient root step and keeps the root step of a
run, whose subject is a variable (`headed_runRoot_unheaded`).  `allHeaded`
heads that one too: the root step of a run is replaced by one root step of a
run for each constructor of atoms other than the run (`headedRunRoots`),

`PrimeStep(space, c(parts), answer) ⊢ run(space, c(parts)) ~> run(space, answer)`.

The evaluator is the evaluator of a region, unchanged: it answers a query of
either kind for any subject pattern by one function
(`regionEvaluator_ambientQuery`, `regionEvaluator_runQuery`), and without a
guard that function answers by stored rules.  The presentation passes the
declaration gate (`allHeaded_validate`), its static equivalence is that of
quotation and dropping (`allHeaded_quoteDropOnly`), and every member respects
it (`allHeaded_respectsStatics`): a family of presented candidates indexed by
the ambient space (`allHeadedMember`).

* **The steps of a run are the runs of the steps of its subject in the member
  at the space of the run** (`allHeaded_run_step_iff`, on terms
  `allHeaded_run_termStep_iff`): under every guard, at every ambient space,
  for every space and every subject.  No hypothesis.  So for every two
  ambient spaces a run has the same steps
  (`allHeaded_run_step_ambient_irrelevant`).
* **A run in a run** (`allHeaded_nested_step_iff`): the steps of
  `run(outer, run(inner, subject))` are the runs of the runs of the steps of
  `subject` in the member at `inner`.  Neither the outer space nor the
  ambient space is in the statement, and nothing is assumed of them.
* **Two runs in one application** (`allHeaded_pair_step_iff`): a step of the
  function in the member at its space, a step of the argument in the member
  at its space, or an answer of the ambient space for the application.
* **No space and no name has a transition, at every stage and under every
  evaluator** (`allHeaded_space_static`, `allHeaded_name_static`).
* **Negative** (`allHeaded_runVariable_normal`): the run of a bound variable
  has no step; no left side matches a bound variable, in a run or outside
  one (`allHeaded_boundVariable_normal`, `headedRunRoots_not_matched_bvar`).

What the presentation hosts, its instances and what it pays are in
`AllHeadedHosting`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

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
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings

variable {lang : LanguageDef} {admits : Pattern → Bool}

/-! ## The eight root steps of a run -/

/-- **The root step of a run of the atoms headed by one constructor**:
`PrimeStep(space, left, answer) ⊢ run(space, left) ~> run(space, answer)`, for
a left side headed by that constructor. -/
def headedRunRootRule (name : String) (left : Pattern) : RewriteRule :=
  { name := name
    typeContext := [("space", .base "Space"), ("answer", .base "Atom")]
    premises := [.relationQuery "PrimeStep" [.fvar "space", left, .fvar "answer"]]
    left := runPattern (.fvar "space") left
    right := runPattern (.fvar "space") (.fvar "answer") }

/-- **The eight root steps of a run**: one for each constructor of atoms other
than the run, with the left sides of the eight root steps. -/
def headedRunRoots : List RewriteRule :=
  [headedRunRootRule "RunRootEquation" (.apply "=" [.fvar "L", .fvar "R"]),
    headedRunRootRule "RunRootUnit" (.apply "prime-unit" []),
    headedRunRootRule "RunRootDrop" (.apply "prime-drop" [.fvar "N"]),
    headedRunRootRule "RunRootVariable" (.apply "prime-variable" [.fvar "I"]),
    headedRunRootRule "RunRootSymbol" (.apply "prime-symbol" [.fvar "I"]),
    headedRunRootRule "RunRootApp" (.apply "App" [.fvar "F", .fvar "X"]),
    headedRunRootRule "RunRootLam" (.apply "Lam" [.fvar "A", .fvar "M"]),
    headedRunRootRule "RunRootPi" (.apply "Pi" [.fvar "A", .fvar "M"])]

/-- **Each of the eight asks for the subject of one of the eight root
steps**: its left side is the run of the left side of that root step, which
is first-order. -/
theorem headedRunRoots_shape : ∀ rule ∈ headedRunRoots,
    ∃ (name rootName label : String) (parameters : List Pattern),
      rule = headedRunRootRule name (.apply label parameters) ∧
        headedRootRule rootName (.apply label parameters) ∈ headedRoots ∧
          isMatchCorrectAux (.apply label parameters) = true := by
  intro rule member
  simp only [headedRunRoots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, "RootEquation", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootUnit", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootDrop", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootVariable", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootSymbol", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootApp", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootLam", _, _, rfl, by simp [headedRoots], by decide⟩
  · exact ⟨_, "RootPi", _, _, rfl, by simp [headedRoots], by decide⟩

/-- The left sides of the eight are the runs of the left sides of the eight
root steps. -/
theorem headedRunRoots_lefts :
    headedRunRoots.map (·.left) =
      headedRoots.map fun rule => runPattern (.fvar "space") rule.left :=
  rfl

/-! ## The presentation -/

/-- **The contained presentation with every root step headed**: the eight
root steps in place of the ambient root step, and the eight root steps of a
run in place of the root step of a run. -/
def allHeaded : LanguageDef :=
  { name := "metta-prime-ambient-space-contained-run-all-roots-headed"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := (fixedRules ++ [releaseRule]) ++ headedRoots ++ spatialCongruences ++
      headedRunRoots ++ [runBetaRule, runReleaseRule, runRunRule] }

theorem allHeaded_rewrites : allHeaded.rewrites =
    [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
      lamBodyRule, releaseRule,
      headedRootRule "RootEquation" (.apply "=" [.fvar "L", .fvar "R"]),
      headedRootRule "RootUnit" (.apply "prime-unit" []),
      headedRootRule "RootDrop" (.apply "prime-drop" [.fvar "N"]),
      headedRootRule "RootVariable" (.apply "prime-variable" [.fvar "I"]),
      headedRootRule "RootSymbol" (.apply "prime-symbol" [.fvar "I"]),
      headedRootRule "RootApp" (.apply "App" [.fvar "F", .fvar "X"]),
      headedRootRule "RootLam" (.apply "Lam" [.fvar "A", .fvar "M"]),
      headedRootRule "RootPi" (.apply "Pi" [.fvar "A", .fvar "M"]),
      runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule,
      runLamBodyRule,
      headedRunRootRule "RunRootEquation" (.apply "=" [.fvar "L", .fvar "R"]),
      headedRunRootRule "RunRootUnit" (.apply "prime-unit" []),
      headedRunRootRule "RunRootDrop" (.apply "prime-drop" [.fvar "N"]),
      headedRunRootRule "RunRootVariable" (.apply "prime-variable" [.fvar "I"]),
      headedRunRootRule "RunRootSymbol" (.apply "prime-symbol" [.fvar "I"]),
      headedRunRootRule "RunRootApp" (.apply "App" [.fvar "F", .fvar "X"]),
      headedRunRootRule "RunRootLam" (.apply "Lam" [.fvar "A", .fvar "M"]),
      headedRunRootRule "RunRootPi" (.apply "Pi" [.fvar "A", .fvar "M"]),
      runBetaRule, runReleaseRule, runRunRule] :=
  rfl

/-- The rewrites of the presentation, in five groups: those of an atom that
ask nothing, the eight root steps, the six congruences beneath a run, the
eight root steps of a run, and beta, release and the step of a run, each
beneath a run. -/
theorem mem_allHeaded_rewrites {rule : RewriteRule} :
    rule ∈ allHeaded.rewrites ↔
      rule ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
        lamBodyRule, releaseRule] ∨ rule ∈ headedRoots ∨ rule ∈ spatialCongruences ∨
        rule ∈ headedRunRoots ∨ rule ∈ [runBetaRule, runReleaseRule, runRunRule] := by
  show rule ∈ (fixedRules ++ [releaseRule]) ++ headedRoots ++ spatialCongruences ++
      headedRunRoots ++ [runBetaRule, runReleaseRule, runRunRule] ↔
    rule ∈ fixedRules ++ [releaseRule] ∨ rule ∈ headedRoots ∨ rule ∈ spatialCongruences ∨
      rule ∈ headedRunRoots ∨ rule ∈ [runBetaRule, runReleaseRule, runRunRule]
  simp only [List.mem_append]
  tauto

theorem allHeaded_mem_plain {rule : RewriteRule}
    (member : rule ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, releaseRule]) : rule ∈ allHeaded.rewrites :=
  mem_allHeaded_rewrites.mpr (.inl member)

theorem allHeaded_mem_root {rule : RewriteRule} (member : rule ∈ headedRoots) :
    rule ∈ allHeaded.rewrites :=
  mem_allHeaded_rewrites.mpr (.inr (.inl member))

theorem allHeaded_mem_spatial {rule : RewriteRule} (member : rule ∈ spatialCongruences) :
    rule ∈ allHeaded.rewrites :=
  mem_allHeaded_rewrites.mpr (.inr (.inr (.inl member)))

theorem allHeaded_mem_runRoot {rule : RewriteRule} (member : rule ∈ headedRunRoots) :
    rule ∈ allHeaded.rewrites :=
  mem_allHeaded_rewrites.mpr (.inr (.inr (.inr (.inl member))))

theorem allHeaded_mem_beneath {rule : RewriteRule}
    (member : rule ∈ [runBetaRule, runReleaseRule, runRunRule]) : rule ∈ allHeaded.rewrites :=
  mem_allHeaded_rewrites.mpr (.inr (.inr (.inr (.inr member))))

theorem allHeaded_typeNames : allHeaded.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem allHeaded_signatures :
    RewriteValidationCertificate.constructorSignatures allHeaded =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem allHeaded_labels :
    RewriteValidationCertificate.constructorLabels allHeaded =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- The rewrites of an atom pass their rows of the declaration gate: those
that ask nothing, and the eight root steps. -/
theorem allHeaded_atomRules_checked :
    ∀ rewrite ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
        lamDomainRule, lamBodyRule, releaseRule] ++ headedRoots,
      RewriteValidationCertificate.check allHeaded rewrite = true := by
  intro rewrite member
  simp only [headedRoots, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
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
      allHeaded_typeNames, allHeaded_signatures, allHeaded_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, headedRootRule,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- The rewrites about a run pass their rows of the declaration gate: the six
congruences beneath a run, the eight root steps of a run, and beta, release
and the step of a run, each beneath a run. -/
theorem allHeaded_runRules_checked :
    ∀ rewrite ∈ spatialCongruences ++ headedRunRoots ++ [runBetaRule, runReleaseRule, runRunRule],
      RewriteValidationCertificate.check allHeaded rewrite = true := by
  intro rewrite member
  simp only [spatialCongruences, headedRunRoots, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
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
      allHeaded_typeNames, allHeaded_signatures, allHeaded_labels,
      betaLeft, appLeft, piLeft, lamLeft, headedRunRootRule, runAppFunctionRule,
      runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule,
      runBetaRule, runReleaseRule, runRunRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- Every rewrite of the presentation passes its row of the declaration
gate. -/
theorem allHeaded_rewrites_checked :
    ∀ rewrite ∈ allHeaded.rewrites,
      RewriteValidationCertificate.check allHeaded rewrite = true := by
  intro rewrite member
  rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
  · exact allHeaded_atomRules_checked rewrite (List.mem_append_left _ plain)
  · exact allHeaded_atomRules_checked rewrite (List.mem_append_right _ root)
  · exact allHeaded_runRules_checked rewrite
      (List.mem_append_left _ (List.mem_append_left _ spatial))
  · exact allHeaded_runRules_checked rewrite
      (List.mem_append_left _ (List.mem_append_right _ runRoot))
  · exact allHeaded_runRules_checked rewrite (List.mem_append_right _ beneath)

/-- **The presentation passes the declaration gate.** -/
theorem allHeaded_validate : allHeaded.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks (lang := allHeaded)
    (RewriteValidationCertificate.validate_signature_of_same_data (left := containedRun) rfl rfl rfl contained_signature_valid) (by decide +kernel) allHeaded_rewrites_checked

/-- The presentation, as a presentation. -/
def allHeadedPresentation : ValidatedLanguageDef := ⟨allHeaded, allHeaded_validate⟩

/-- **It differs from `headedContained` by the root step of a run alone**:
the same constructors, the same equation, and the twenty-five rewrites of
`headedContained` other than the root step of a run. -/
theorem allHeaded_differs :
    allHeaded.terms = headedContained.terms ∧
      allHeaded.equations = headedContained.equations ∧
        (∀ rule ∈ headedContained.rewrites, rule ≠ runRewrite → rule ∈ allHeaded.rewrites) ∧
          runRewrite.name ∉ allHeaded.rewrites.map (·.name) := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  intro rule member other
  rw [headedContained_rewrites] at member
  rw [allHeaded_rewrites]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

/-! ## Its static equivalence -/

/-- **The static equivalence is that of quotation and dropping.** -/
theorem allHeaded_quoteDropOnly : QuoteDropOnly allHeaded :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem allHeaded_quoteDropSorted : QuoteDropSorted allHeaded :=
  ⟨by decide, by decide⟩

theorem allHeaded_carriesAtoms : CarriesAtoms allHeaded := by
  unfold CarriesAtoms
  decide

theorem allHeaded_declaresRun : DeclaresRun allHeaded := by
  unfold DeclaresRun
  decide

theorem allHeaded_namesOnlyDropped : NamesOnlyDropped allHeaded unquotedSorts :=
  atomsReduce_namesOnlyDropped

/-! ## The evaluator is the evaluator of a region, unchanged -/

/-- **What the evaluator answers to a query of the root step of a run for any
subject pattern**: the answers of the space of the run for the instance of
the subject.  The eight root steps of a run ask such queries; the evaluator
is not changed for them. -/
theorem regionEvaluator_runQuery (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang : LanguageDef) (bindings : Bindings) (subject : Pattern) :
    regionEvaluator admits ambientSpace lang bindings
        (.relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) =
      (admittedAnswers admits (applyBindings bindings (.fvar "space"))
        (applyBindings bindings subject)).map fun result => ("answer", result) :: bindings :=
  rfl

/-- **The evaluator of a region respects the static equivalence** in every
language whose static equivalence is that of quotation and dropping and whose
premises are a query of the ambient root step or of the root step of a run
for a first-order subject, or congruences. -/
theorem regionEvaluator_respectsStatics_of_headedQueries {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (premises : ∀ premise ∈ presentedPremises lang,
      (∃ subject, isMatchCorrectAux subject = true ∧
        premise = .relationQuery "AmbientStep" [subject, .fvar "answer"]) ∨
      (∃ subject, isMatchCorrectAux subject = true ∧
        premise = .relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) ∨
      ∃ source target, premise = .congruence source target)
    (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (only.equiv equivalent).1
  rcases premises premise member with ⟨subject, exact, rfl⟩ | ⟨subject, exact, rfl⟩ |
    ⟨source, target, rfl⟩
  · have answers : result ∈ (admittedAnswers admits ambientSpace
        (applyBindings first subject)).map fun answer => ("answer", answer) :: first := answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [admittedAnswers_congr admits rfl
      (contract_applyBindings_congr contractions subject exact)] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (admittedAnswers admits ambientSpace
      (applyBindings second subject)).map fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · have answers : result ∈ (admittedAnswers admits (applyBindings first (.fvar "space"))
        (applyBindings first subject)).map fun answer => ("answer", answer) :: first := answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [admittedAnswers_congr admits
      (contract_applyBindings_congr contractions (.fvar "space") rfl)
      (contract_applyBindings_congr contractions subject exact)] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (admittedAnswers admits (applyBindings second (.fvar "space"))
      (applyBindings second subject)).map fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [regionEvaluator] at answered

/-- The premises that the presentation hands to its evaluator. -/
theorem allHeaded_premises : ∀ premise ∈ presentedPremises allHeaded,
    (∃ subject, isMatchCorrectAux subject = true ∧
      premise = .relationQuery "AmbientStep" [subject, .fvar "answer"]) ∨
    (∃ subject, isMatchCorrectAux subject = true ∧
      premise = .relationQuery "PrimeStep" [.fvar "space", subject, .fvar "answer"]) ∨
    ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      ([.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .relationQuery "AmbientStep" [.apply "=" [.fvar "L", .fvar "R"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "prime-unit" [], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "prime-drop" [.fvar "N"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "prime-variable" [.fvar "I"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "prime-symbol" [.fvar "I"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "App" [.fvar "F", .fvar "X"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "Lam" [.fvar "A", .fvar "M"], .fvar "answer"],
        .relationQuery "AmbientStep" [.apply "Pi" [.fvar "A", .fvar "M"], .fvar "answer"],
        .congruence (runPattern (.fvar "space") (.fvar "F")) (runPattern (.fvar "space") (.fvar "G")),
        .congruence (runPattern (.fvar "space") (.fvar "X")) (runPattern (.fvar "space") (.fvar "Y")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "=" [.fvar "L", .fvar "R"], .fvar "answer"],
        .relationQuery "PrimeStep" [.fvar "space", .apply "prime-unit" [], .fvar "answer"],
        .relationQuery "PrimeStep" [.fvar "space", .apply "prime-drop" [.fvar "N"], .fvar "answer"],
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "prime-variable" [.fvar "I"], .fvar "answer"],
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "prime-symbol" [.fvar "I"], .fvar "answer"],
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "App" [.fvar "F", .fvar "X"], .fvar "answer"],
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "Lam" [.fvar "A", .fvar "M"], .fvar "answer"],
        .relationQuery "PrimeStep"
          [.fvar "space", .apply "Pi" [.fvar "A", .fvar "M"], .fvar "answer"],
        .congruence (runPattern (.fvar "space") (.fvar "X"))
          (runPattern (.fvar "space") (.fvar "Y"))] : List Premise) :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inr (.inr ⟨_, _, rfl⟩)
    | exact .inl ⟨_, by decide, rfl⟩
    | exact .inr (.inl ⟨_, by decide, rfl⟩)

/-- **Every member respects the static equivalence of the presentation**,
under every guard. -/
theorem allHeaded_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) allHeaded :=
  regionEvaluator_respectsStatics_of_headedQueries allHeaded_quoteDropOnly allHeaded_premises
    admits ambientSpace

/-- A space of the presentation. -/
abbrev AllHeadedSpace : Type := Contexts.Term allHeaded closedSpace

/-- **The member of the family at an ambient space**, as a presented
candidate: the presentation under the evaluator of a region. -/
def allHeadedMember (admits : Pattern → Bool) (space : AllHeadedSpace) : PresentedCandidate where
  presentation := allHeadedPresentation
  evaluator := regionEvaluator admits space.1
  respects := allHeaded_respectsStatics admits space.1

/-- The theory of the presentation at an ambient space, with all its
contexts. -/
abbrev allHeadedTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) allHeadedPresentation

/-! ## A root step of a run by one of the eight, on patterns -/

/-- The instance of the right side of a root step of a run. -/
theorem apply_headedRunRootRule (name : String) (left : Pattern) {initial : Bindings}
    {space : Pattern} (spaceValue : applyBindings initial (.fvar "space") = space)
    (answer : Pattern) :
    applyRuleBindings (headedRunRootRule name left) (("answer", answer) :: initial) =
      runPattern space answer := by
  rw [← spaceValue]
  simp [applyRuleBindings, headedRunRootRule, runPattern, applyBindings]

/-- **A headed root step of a run**: from the run of a pattern that the left
side matches to the run of an answer of the space of the run for it that the
guard admitted.  The ambient space is not asked. -/
theorem step_headedRunRoot {ambientSpace : Pattern} {name : String} {left : Pattern}
    (member : headedRunRootRule name left ∈ lang.rewrites) {space subject answer : Pattern}
    {initial : Bindings}
    (matched : initial ∈ matchPattern (runPattern (.fvar "space") left) (runPattern space subject))
    (spaceValue : applyBindings initial (.fvar "space") = space)
    (rebuilt : applyBindings initial left = subject)
    (found : answer ∈ admittedAnswers admits space subject) :
    StepAt (regionEvaluator admits ambientSpace) lang 1 (runPattern space subject)
      (runPattern space answer) := by
  refine stepAt_of_rule (rule := headedRunRootRule name left) member (initial := initial)
    (final := ("answer", answer) :: initial) matched ?_
    (apply_headedRunRootRule name left spaceValue answer)
  refine .cons (.relationQuery ?_) (.nil _)
  show _ ∈ (admittedAnswers admits (applyBindings initial (.fvar "space"))
    (applyBindings initial left)).map fun result => ("answer", result) :: initial
  rw [spaceValue, rebuilt]
  exact List.mem_map.mpr ⟨answer, found, rfl⟩

/-- What a headed root step of a run is: the run of an answer of the space of
the run for its subject, which the left side of the root step matches. -/
theorem headedRunRoot_inv {ambientSpace : Pattern} {name : String} {left : Pattern}
    (exact : isMatchCorrectAux left = true) {fuel : Nat} {source : Pattern}
    {initial final : Bindings}
    (matched : initial ∈ matchPattern (headedRunRootRule name left).left source)
    (premises : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      (headedRunRootRule name left).premises final) :
    ∃ (space subject answer : Pattern) (inner : Bindings), source = runPattern space subject ∧
      inner ∈ matchPattern left subject ∧ applyBindings initial (.fvar "space") = space ∧
        applyBindings initial left = subject ∧ answer ∈ admittedAnswers admits space subject ∧
          applyRuleBindings (headedRunRootRule name left) final = runPattern space answer := by
  have matchedRun : initial ∈ matchPattern (.apply "prime-run" [.fvar "space", left]) source :=
    matched
  obtain ⟨space, subject, outer, inner, rfl, -, inSubject, -⟩ :=
    matched_apply_two (label := "prime-run") matchedRun
  have exactRun : isMatchCorrectAux (.apply "prime-run" [.fvar "space", left]) = true := by
    simp [isMatchCorrectAux, isMatchCorrectListAux, exact]
  have rebuiltRun := matchPattern_correct matchedRun exactRun
  have parts : applyBindings initial (.fvar "space") = space ∧
      applyBindings initial left = subject := by
    have unfolded : Pattern.apply "prime-run"
        [applyBindings initial (.fvar "space"), applyBindings initial left] =
          .apply "prime-run" [space, subject] := by
      rw [← rebuiltRun]
      conv_rhs => rw [applyBindings]
      rfl
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
    exact unfolded
  have premises' : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      [.relationQuery "PrimeStep" [.fvar "space", left, .fvar "answer"]] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (admittedAnswers admits (applyBindings initial (.fvar "space"))
              (applyBindings initial left)).map fun result => ("answer", result) :: initial :=
            answered
          rw [parts.1, parts.2] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          exact ⟨space, subject, answer, inner, rfl, inSubject, parts.1, parts.2, found,
            apply_headedRunRootRule name left parts.1 answer⟩

/-- **Negative**: no headed root step of a run matches the run of a bound
variable. -/
theorem headedRunRoots_not_matched_bvar {rule : RewriteRule} (member : rule ∈ headedRunRoots)
    {space : Pattern} {index : Nat} {bindings : Bindings} :
    bindings ∉ matchPattern rule.left (runPattern space (.bvar index)) := by
  obtain ⟨name, rootName, label, parameters, rfl, -, -⟩ := headedRunRoots_shape rule member
  intro matched
  have matchedRun : bindings ∈ matchPattern
      (.apply "prime-run" [.fvar "space", .apply label parameters])
      (.apply "prime-run" [space, .bvar index]) := matched
  obtain ⟨otherSpace, subject, outer, inner, shape, -, inSubject, -⟩ :=
    matched_apply_two (label := "prime-run") matchedRun
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
  obtain ⟨-, rfl⟩ := shape
  exact bvar_not_matched inSubject

/-- Every rewrite about a run has a run as its left side. -/
theorem allHeaded_runRule_left {rule : RewriteRule}
    (member : rule ∈ spatialCongruences ∨ rule ∈ headedRunRoots ∨
      rule ∈ [runBetaRule, runReleaseRule, runRunRule]) :
    ∃ left right, rule.left = runPattern left right := by
  rcases member with spatial | runRoot | beneath
  · simp only [spatialCongruences, List.mem_cons, List.not_mem_nil, or_false] at spatial
    rcases spatial with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · obtain ⟨name, rootName, label, parameters, rfl, -, -⟩ := headedRunRoots_shape rule runRoot
    exact ⟨_, _, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at beneath
    rcases beneath with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-! ## Only an atom has a transition, at every stage -/

/-- **Every rewrite of the presentation is headed by a constructor of
atoms.** -/
theorem allHeaded_headedIn_atom : rewritesHeadedIn allHeaded ["Atom"] = true := by decide

/-- **No space has a transition**, at every stage and under every
evaluator. -/
theorem allHeaded_space_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term allHeaded ⟨.base "Space", stage⟩) :
    ¬ TermStep base allHeaded term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts allHeaded_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-- **No name has a transition**, at every stage and under every
evaluator. -/
theorem allHeaded_name_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term allHeaded ⟨.base "CandidateName", stage⟩) :
    ¬ TermStep base allHeaded term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts allHeaded_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-- Every left side of the presentation is an application. -/
theorem allHeaded_left_apply : ∀ rule ∈ allHeaded.rewrites,
    ∃ label parameters, rule.left = .apply label parameters := by
  intro rule member
  rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
    rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · obtain ⟨name, label, parameters, rfl, -, -⟩ := headedRoots_shape rule root
    exact ⟨_, _, rfl⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
    exact ⟨_, _, shape⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
    exact ⟨_, _, shape⟩
  · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
    exact ⟨_, _, shape⟩

/-- **A bound variable has no step**, under every evaluator. -/
theorem allHeaded_boundVariable_normal {base : BasePremiseEvaluator} (index : Nat)
    (target : Pattern) : ¬ Step base allHeaded (.bvar index) target := by
  rintro ⟨fuel, step⟩
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, -, -⟩ := exists_rule_of_stepAt step
      obtain ⟨label, parameters, left⟩ := allHeaded_left_apply rule member
      rw [left] at matched
      exact bvar_not_matched matched

/-! ## A step of a run does not consult the ambient space -/

/-- **A step of a run at one ambient space leads to a run in the same space,
and is a step of that run at every ambient space.** -/
theorem allHeaded_run_stepAt_ambient_irrelevant (first second : Pattern) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits first) allHeaded fuel (runPattern space subject) target →
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator admits second) allHeaded (runPattern space subject)
            (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · exact absurd matched (headedRoots_not_matched_run root)
      · simp only [spatialCongruences, List.mem_cons, List.not_mem_nil, or_false] at spatial
        rcases spatial with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppFunction_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runAppFunction
            (allHeaded_mem_spatial (by simp [spatialCongruences])) argument lifted⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppArgument_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runAppArgument
            (allHeaded_mem_spatial (by simp [spatialCongruences])) function lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runPiDomain
            (allHeaded_mem_spatial (by simp [spatialCongruences])) body binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runPiBody
            (allHeaded_mem_spatial (by simp [spatialCongruences])) domain binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runLamDomain
            (allHeaded_mem_spatial (by simp [spatialCongruences])) body binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runLamBody
            (allHeaded_mem_spatial (by simp [spatialCongruences])) domain binder lifted⟩
      · obtain ⟨name, rootName, label, parameters, rfl, -, exact⟩ :=
          headedRunRoots_shape rule runRoot
        obtain ⟨otherSpace, inner, answer, bindings, shape, -, spaceValue, rebuilt, found,
          applied⟩ := headedRunRoot_inv exact matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨answer, applied, 1, step_headedRunRoot (allHeaded_mem_runRoot runRoot) matched
          spaceValue rebuilt found⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at beneath
        rcases beneath with rfl | rfl | rfl
        · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
            runBeta_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨_, applied, 1, step_runBeta (allHeaded_mem_beneath (by simp)) _ domain body
            argument binder⟩
        · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨_, applied, 1, step_runRelease (allHeaded_mem_beneath (by simp)) _ atom⟩
        · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
            runBeneathRun_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih innerStep
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_runBeneathRun (allHeaded_mem_beneath (by simp)) _
            lifted⟩

/-- A step of a run in the member at a space is a step of the run of that run
in the space, at every ambient space. -/
theorem allHeaded_run_of_run_stepAt (space ambientSpace : Pattern) {fuel : Nat}
    {inner innerSubject target : Pattern}
    (step : StepAt (regionEvaluator admits space) allHeaded fuel
      (runPattern inner innerSubject) target) :
    Step (regionEvaluator admits ambientSpace) allHeaded
      (runPattern space (runPattern inner innerSubject)) (runPattern space target) := by
  obtain ⟨reached, rfl, count, lifted⟩ :=
    allHeaded_run_stepAt_ambient_irrelevant space ambientSpace fuel step
  exact ⟨count + 1, step_runBeneathRun (allHeaded_mem_beneath (by simp)) space lifted⟩

/-! ## A step of a run is the run of a step of its subject at its space -/

/-- **A step of a pattern in the member at a space is a step of its run in
that space, at every ambient space.** -/
theorem allHeaded_run_of_stepAt {space : Pattern} (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {subject next : Pattern},
      StepAt (regionEvaluator admits space) allHeaded fuel subject next →
        Step (regionEvaluator admits ambientSpace) allHeaded (runPattern space subject)
          (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro subject next step; cases step
  | succ fuel ih =>
      intro subject next step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
          rw [applied]
          exact ⟨1, step_runBeta (allHeaded_mem_beneath (by simp)) space domain body argument
            binder⟩
        · obtain ⟨function, argument, moved, rfl, inner, applied⟩ :=
            appFunction_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppFunction
            (allHeaded_mem_spatial (by simp [spatialCongruences])) argument lifted⟩
        · obtain ⟨function, argument, moved, rfl, inner, applied⟩ :=
            appArgument_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppArgument
            (allHeaded_mem_spatial (by simp [spatialCongruences])) function lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiDomain
            (allHeaded_mem_spatial (by simp [spatialCongruences])) body binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiBody
            (allHeaded_mem_spatial (by simp [spatialCongruences])) domain binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ :=
            lamDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamDomain
            (allHeaded_mem_spatial (by simp [spatialCongruences])) body binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamBody
            (allHeaded_mem_spatial (by simp [spatialCongruences])) domain binder lifted⟩
        · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
          rw [applied]
          exact ⟨1, step_runRelease (allHeaded_mem_beneath (by simp)) space atom⟩
      · simp only [headedRoots, List.mem_cons, List.not_mem_nil, or_false] at root
        rcases root with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨left, right, -, -, rfl, -, -, -⟩ := matched_apply_two (label := "=") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootEquation")
            (left := .apply "=" [.fvar "L", .fvar "R"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("L", left), ("R", right), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨arguments, rfl, length⟩ := eq_apply_of_matched matched
          obtain rfl : arguments = [] := List.eq_nil_of_length_eq_zero length
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootUnit") (left := .apply "prime-unit" [])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨name, rfl, -⟩ := matched_apply_one (label := "prime-drop") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootDrop")
            (left := .apply "prime-drop" [.fvar "N"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("N", name), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨index, rfl, -⟩ := matched_apply_one (label := "prime-variable") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootVariable")
            (left := .apply "prime-variable" [.fvar "I"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("I", index), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨index, rfl, -⟩ := matched_apply_one (label := "prime-symbol") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootSymbol")
            (left := .apply "prime-symbol" [.fvar "I"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("I", index), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨left, right, -, -, rfl, -, -, -⟩ := matched_apply_two (label := "App") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootApp")
            (left := .apply "App" [.fvar "F", .fvar "X"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("F", left), ("X", right), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨left, right, -, -, rfl, -, -, -⟩ := matched_apply_two (label := "Lam") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootLam")
            (left := .apply "Lam" [.fvar "A", .fvar "M"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("A", left), ("M", right), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
        · obtain ⟨answer, found, applied⟩ := headedRoot_inv (by decide) matched premises
          obtain ⟨left, right, -, -, rfl, -, -, -⟩ := matched_apply_two (label := "Pi") matched
          rw [applied]
          exact ⟨1, step_headedRunRoot (name := "RunRootPi")
            (left := .apply "Pi" [.fvar "A", .fvar "M"])
            (allHeaded_mem_runRoot (by simp [headedRunRoots]))
            (initial := [("A", left), ("M", right), ("space", space)])
            (by simp [runPattern, matchPattern, matchArgs, mergeBindings])
            (by simp [applyBindings]) (by simp [applyBindings]) found⟩
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
        rw [shape] at matched
        obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact allHeaded_run_of_run_stepAt space ambientSpace step
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
        rw [shape] at matched
        obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact allHeaded_run_of_run_stepAt space ambientSpace step
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
        rw [shape] at matched
        obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact allHeaded_run_of_run_stepAt space ambientSpace step

/-- **A step of a run is the run of a step of its subject in the member at the
space of the run**, at every ambient space. -/
theorem allHeaded_run_stepAt_inv (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) allHeaded fuel (runPattern space subject)
          target →
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator admits space) allHeaded subject next := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · exact absurd matched (headedRoots_not_matched_run root)
      · simp only [spatialCongruences, List.mem_cons, List.not_mem_nil, or_false] at spatial
        rcases spatial with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppFunction_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_appFunction (allHeaded_mem_plain (by simp)) argument
            lifted⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppArgument_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_appArgument (allHeaded_mem_plain (by simp)) function
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_piDomain (allHeaded_mem_plain (by simp)) body binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_piBody (allHeaded_mem_plain (by simp)) domain binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_lamDomain (allHeaded_mem_plain (by simp)) body binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, count, lifted⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, count + 1, step_lamBody (allHeaded_mem_plain (by simp)) domain binder
            lifted⟩
      · obtain ⟨name, rootName, label, parameters, rfl, paired, exact⟩ :=
          headedRunRoots_shape rule runRoot
        obtain ⟨otherSpace, inner, answer, bindings, shape, innerMatched, -, -, found, applied⟩ :=
          headedRunRoot_inv exact matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨answer, applied, 1, step_headedRoot (allHeaded_mem_root paired) innerMatched
          (matchPattern_correct innerMatched exact) found⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at beneath
        rcases beneath with rfl | rfl | rfl
        · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
            runBeta_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨_, applied, 1, step_beta (allHeaded_mem_plain (by simp)) domain body argument
            binder⟩
        · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨_, applied, 1, step_release (allHeaded_mem_plain (by simp)) atom⟩
        · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
            runBeneathRun_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, lifted⟩ :=
            allHeaded_run_stepAt_ambient_irrelevant ambientSpace _ fuel innerStep
          obtain ⟨-, rfl⟩ := runPattern_injective same
          exact ⟨_, applied, lifted⟩

/-- **The steps of a run are the runs of the steps of its subject in the
member at the space of the run**: under every guard, at every ambient space,
for every space and every subject.  The run constructor puts the member at
its space inside every other member. -/
theorem allHeaded_run_step_iff {ambientSpace space subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) allHeaded (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (regionEvaluator admits space) allHeaded subject next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact allHeaded_run_stepAt_inv ambientSpace fuel step
  · rintro ⟨next, rfl, fuel, step⟩
    exact allHeaded_run_of_stepAt ambientSpace fuel step

/-- **For every two ambient spaces a run has the same steps.** -/
theorem allHeaded_run_step_ambient_irrelevant (first second : Pattern)
    {space subject target : Pattern} :
    Step (regionEvaluator admits first) allHeaded (runPattern space subject) target ↔
      Step (regionEvaluator admits second) allHeaded (runPattern space subject) target :=
  allHeaded_run_step_iff.trans allHeaded_run_step_iff.symm

/-- **A run in a run**: its steps are the runs of the runs of the steps of the
inner subject in the member at the inner space.  The outer space and the
ambient space are not in the statement, and nothing is assumed of them. -/
theorem allHeaded_nested_step_iff {ambientSpace outer inner subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) allHeaded
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        Step (regionEvaluator admits inner) allHeaded subject next := by
  rw [allHeaded_run_step_iff]
  constructor
  · rintro ⟨reached, rfl, step⟩
    obtain ⟨next, rfl, innerStep⟩ := allHeaded_run_step_iff.mp step
    exact ⟨next, rfl, innerStep⟩
  · rintro ⟨next, rfl, step⟩
    exact ⟨_, rfl, allHeaded_run_step_iff.mpr ⟨next, rfl, step⟩⟩

/-- **The run of a bound variable has no step**, under every guard and at
every ambient space: no root step of a run matches it. -/
theorem allHeaded_runVariable_normal (ambientSpace space : Pattern) (index : Nat)
    (target : Pattern) :
    ¬ Step (regionEvaluator admits ambientSpace) allHeaded (runPattern space (.bvar index))
      target := by
  intro step
  obtain ⟨next, -, inner⟩ := allHeaded_run_step_iff.mp step
  exact allHeaded_boundVariable_normal index next inner

/-! ## Two runs in one application -/

/-- **The steps of an application of two runs**, at every ambient space: a
step of the function in the member at its space, a step of the argument in
the member at its space, or an answer of the ambient space for the
application. -/
theorem allHeaded_pair_step_iff {ambientSpace first second function argument target : Pattern} :
    Step (regionEvaluator admits ambientSpace) allHeaded
        (.apply "App" [runPattern first function, runPattern second argument]) target ↔
      (∃ next, target = .apply "App" [runPattern first next, runPattern second argument] ∧
        Step (regionEvaluator admits first) allHeaded function next) ∨
      (∃ next, target = .apply "App" [runPattern first function, runPattern second next] ∧
        Step (regionEvaluator admits second) allHeaded argument next) ∨
      target ∈ admittedAnswers admits ambientSpace
        (.apply "App" [runPattern first function, runPattern second argument]) := by
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
        rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
          rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨domain, binder, body, value, shape, -⟩ := beta_inv matched premises
            simp [runPattern] at shape
          · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
              appFunction_inv matched premises
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
            obtain ⟨rfl, rfl⟩ := shape
            obtain ⟨next, rfl, movedStep⟩ := allHeaded_run_stepAt_inv ambientSpace fuel inner
            exact .inl ⟨next, applied, movedStep⟩
          · obtain ⟨functionPattern, argumentPattern, moved, shape, inner, applied⟩ :=
              appArgument_inv matched premises
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
            obtain ⟨rfl, rfl⟩ := shape
            obtain ⟨next, rfl, movedStep⟩ := allHeaded_run_stepAt_inv ambientSpace fuel inner
            exact .inr (.inl ⟨next, applied, movedStep⟩)
          · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Pi") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
          · exact absurd matched (apply_not_matched (label := "Lam") (other := "App") (by decide))
          · exact absurd matched
              (apply_not_matched (label := "prime-drop") (other := "App") (by decide))
        · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
          obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
          exact .inr (.inr (applied ▸ found))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
          rw [shape] at matched
          exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
          rw [shape] at matched
          exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
        · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
          rw [shape] at matched
          exact absurd matched (apply_not_matched (label := "prime-run") (other := "App") (by decide))
  · rintro (⟨next, rfl, fuel, step⟩ | ⟨next, rfl, fuel, step⟩ | found)
    · obtain ⟨count, lifted⟩ := allHeaded_run_of_stepAt ambientSpace fuel step
      exact ⟨count + 1, step_appFunction (allHeaded_mem_plain (by simp)) _ lifted⟩
    · obtain ⟨count, lifted⟩ := allHeaded_run_of_stepAt ambientSpace fuel step
      exact ⟨count + 1, step_appArgument (allHeaded_mem_plain (by simp)) _ lifted⟩
    · exact ⟨1, step_headedRoot (name := "RootApp") (left := .apply "App" [.fvar "F", .fvar "X"])
        (allHeaded_mem_root (by simp [headedRoots]))
        (initial := [("X", runPattern second argument), ("F", runPattern first function)])
        (by simp [matchPattern, matchArgs, mergeBindings]) (by simp [applyBindings]) found⟩

/-! ## On terms -/

/-- **On terms: the transitions of `run(space, atom)` are the runs of the
transitions of `atom` in the member at `space`**, under every guard and at
every ambient space. -/
theorem allHeaded_run_termStep_iff {ambientSpace : Pattern} {stage : List TypeExpr}
    (space : Contexts.Term allHeaded ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term allHeaded ⟨.base "Atom", stage⟩) :
    TermStep (regionEvaluator admits ambientSpace) allHeaded
        (runTermIn allHeaded_declaresRun space atom) target ↔
      ∃ next : Contexts.Term allHeaded ⟨.base "Atom", stage⟩,
        TermStep (regionEvaluator admits space.1) allHeaded atom next ∧
          (termSetoid (regionEvaluator admits ambientSpace) allHeaded ⟨.base "Atom", stage⟩).r
            target (runTermIn allHeaded_declaresRun space next) := by
  constructor
  · rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩
    obtain ⟨otherSpace, otherAtom, rfl, spaceSame, atomSame⟩ :=
      eq_runTermIn_of_related allHeaded_quoteDropOnly allHeaded_quoteDropSorted
        allHeaded_declaresRun before
    obtain ⟨reached, shape, moved⟩ := allHeaded_run_stepAt_inv ambientSpace fuel fired
    obtain ⟨reachedSpace, reachedAtom, rfl, reachedSpaceVal, rfl⟩ :=
      eq_runTermIn_of_val allHeaded_declaresRun contractum shape
    rw [regionEvaluator_congr admits spaceSame] at moved
    refine ⟨reachedAtom, ⟨otherAtom, reachedAtom, ?_, moved, Relation.EqvGen.refl _⟩, ?_⟩
    · exact (allHeaded_quoteDropOnly.termSetoid_iff allHeaded_quoteDropSorted).mpr atomSame.symm
    · refine (termSetoid (regionEvaluator admits ambientSpace) allHeaded _).iseqv.trans
        ((termSetoid (regionEvaluator admits ambientSpace) allHeaded _).iseqv.symm after) ?_
      refine (runTermIn_related_iff allHeaded_quoteDropOnly allHeaded_quoteDropSorted
        allHeaded_declaresRun).mpr ⟨?_, rfl⟩
      rw [reachedSpaceVal]
      exact spaceSame
  · rintro ⟨next, ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩, related⟩
    refine ⟨runTermIn allHeaded_declaresRun space redex,
      runTermIn allHeaded_declaresRun space contractum, ?_,
      allHeaded_run_of_stepAt ambientSpace fuel fired, ?_⟩
    · exact (runTermIn_related_iff allHeaded_quoteDropOnly allHeaded_quoteDropSorted
        allHeaded_declaresRun).mpr ⟨rfl, allHeaded_quoteDropOnly.contract_eq before⟩
    · refine (termSetoid (regionEvaluator admits ambientSpace) allHeaded _).iseqv.trans ?_
        ((termSetoid (regionEvaluator admits ambientSpace) allHeaded _).iseqv.symm related)
      exact (runTermIn_related_iff allHeaded_quoteDropOnly allHeaded_quoteDropSorted
        allHeaded_declaresRun).mpr ⟨rfl, allHeaded_quoteDropOnly.contract_eq after⟩

#print axioms headedRunRoots_shape
#print axioms headedRunRoots_lefts
#print axioms allHeaded_rewrites
#print axioms mem_allHeaded_rewrites
#print axioms allHeaded_validate
#print axioms allHeaded_differs
#print axioms allHeaded_quoteDropOnly
#print axioms regionEvaluator_runQuery
#print axioms regionEvaluator_respectsStatics_of_headedQueries
#print axioms allHeaded_respectsStatics
#print axioms allHeadedMember
#print axioms step_headedRunRoot
#print axioms headedRunRoot_inv
#print axioms headedRunRoots_not_matched_bvar
#print axioms allHeaded_headedIn_atom
#print axioms allHeaded_space_static
#print axioms allHeaded_name_static
#print axioms allHeaded_boundVariable_normal
#print axioms allHeaded_run_stepAt_ambient_irrelevant
#print axioms allHeaded_run_of_stepAt
#print axioms allHeaded_run_stepAt_inv
#print axioms allHeaded_run_step_iff
#print axioms allHeaded_run_step_ambient_irrelevant
#print axioms allHeaded_nested_step_iff
#print axioms allHeaded_runVariable_normal
#print axioms allHeaded_pair_step_iff
#print axioms allHeaded_run_termStep_iff
#print axioms allHeaded_mem_plain
#print axioms allHeaded_mem_root
#print axioms allHeaded_mem_spatial
#print axioms allHeaded_mem_runRoot
#print axioms allHeaded_mem_beneath
#print axioms allHeaded_typeNames
#print axioms allHeaded_signatures
#print axioms allHeaded_labels
#print axioms allHeaded_atomRules_checked
#print axioms allHeaded_runRules_checked
#print axioms allHeaded_rewrites_checked
#print axioms allHeaded_quoteDropSorted
#print axioms allHeaded_carriesAtoms
#print axioms allHeaded_declaresRun
#print axioms allHeaded_namesOnlyDropped
#print axioms allHeaded_premises
#print axioms apply_headedRunRootRule
#print axioms allHeaded_runRule_left
#print axioms allHeaded_left_apply
#print axioms allHeaded_run_of_run_stepAt

end Mettapedia.Logic.HostingStyles.AmbientRegions
