import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AmbientRegions.WeakEvaluator

/-!
# Root steps headed by the constructors of atoms: a third presentation

The ambient root step has a variable as left side.  Two consequences were
found: a term that is no atom has a root step, and the ambient space is asked
for a run.  A guard in the evaluator removes both and costs the weakness of
the evaluator (`guarded_not_answersByStoredRules`).

This module removes both **in the presentation**, with the evaluator
unchanged: the one ambient root step is replaced by one root step for each
constructor of atoms other than the run (`headedRoots`), each with a left side
headed by its constructor:

`AmbientStep(c(parts), answer) ⊢ c(parts) ~> answer`.

`headedContained` is the contained presentation with these eight root steps
in place of `rootRule`.  It passes the declaration gate
(`headedContained_validate`), its static equivalence is that of quotation and
dropping (`headedContained_quoteDropOnly`), and the evaluator of a region
respects it under every guard (`headedContained_respectsStatics`), so it is a
family of presented candidates indexed by the ambient space
(`headedMember`).

What a root step by one of the eight is, on patterns: `step_headedRoot`,
`headedRoot_inv`.  No left side is a variable, a bound variable or a run
(`headedRoots_shape`), so **a bound variable has no root step**: this is what
the presentation pays (`HeadedContainment`).
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

/-! ## The eight root steps -/

/-- **The root step of the atoms headed by one constructor**:
`AmbientStep(left, answer) ⊢ left ~> answer`, for a left side headed by that
constructor. -/
def headedRootRule (name : String) (left : Pattern) : RewriteRule :=
  { name := name
    typeContext := [("answer", .base "Atom")]
    premises := [.relationQuery "AmbientStep" [left, .fvar "answer"]]
    left := left
    right := .fvar "answer" }

/-- **The eight root steps**: one for each constructor of atoms other than
the run.  An abstraction and a product are matched with their second argument
as a whole. -/
def headedRoots : List RewriteRule :=
  [headedRootRule "RootEquation" (.apply "=" [.fvar "L", .fvar "R"]),
    headedRootRule "RootUnit" (.apply "prime-unit" []),
    headedRootRule "RootDrop" (.apply "prime-drop" [.fvar "N"]),
    headedRootRule "RootVariable" (.apply "prime-variable" [.fvar "I"]),
    headedRootRule "RootSymbol" (.apply "prime-symbol" [.fvar "I"]),
    headedRootRule "RootApp" (.apply "App" [.fvar "F", .fvar "X"]),
    headedRootRule "RootLam" (.apply "Lam" [.fvar "A", .fvar "M"]),
    headedRootRule "RootPi" (.apply "Pi" [.fvar "A", .fvar "M"])]

/-- The heads of the eight left sides. -/
def atomRootHeads : List String :=
  ["=", "prime-unit", "prime-drop", "prime-variable", "prime-symbol", "App", "Lam", "Pi"]

/-- **Each of the eight has a first-order left side headed by a constructor
of atoms other than the run.** -/
theorem headedRoots_shape : ∀ rule ∈ headedRoots,
    ∃ (name label : String) (parameters : List Pattern),
      rule = headedRootRule name (.apply label parameters) ∧
        isMatchCorrectAux (.apply label parameters) = true ∧ label ∈ atomRootHeads := by
  intro rule member
  simp only [headedRoots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, by decide, by decide⟩

/-- **Positive**: every constructor of atoms other than the run heads one of
them. -/
theorem atomRootHeads_cover :
    ∀ rule ∈ atomsReduce.terms, rule.category = "Atom" → rule.label ≠ "prime-run" →
      rule.label ∈ atomRootHeads := by
  decide

/-- **Negative**: the run heads none, and neither does a constructor of
spaces or quotation. -/
theorem atomRootHeads_exclude :
    "prime-run" ∉ atomRootHeads ∧ "prime-space-empty" ∉ atomRootHeads ∧
      "prime-space-add" ∉ atomRootHeads ∧ "prime-quote" ∉ atomRootHeads := by
  decide

/-! ## The presentation -/

/-- **The contained presentation with headed root steps**: the contained
presentation, with the eight root steps in place of the ambient root step. -/
def headedContained : LanguageDef :=
  { name := "metta-prime-ambient-space-contained-run-headed-roots"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := (fixedRules ++ [releaseRule]) ++ headedRoots ++
      (sharedRunRules ++ [runBetaRule, runReleaseRule, runRunRule]) }

theorem headedContained_rewrites : headedContained.rewrites =
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
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runBetaRule, runReleaseRule, runRunRule] :=
  rfl

/-- The rewrites of the presentation, in three groups: those of an atom that
ask nothing, the eight root steps, and those about a run. -/
theorem mem_headedContained_rewrites {rule : RewriteRule} :
    rule ∈ headedContained.rewrites ↔
      rule ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
        lamBodyRule, releaseRule] ∨ rule ∈ headedRoots ∨
        rule ∈ [runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule,
          runPiBodyRule, runLamDomainRule, runLamBodyRule, runBetaRule, runReleaseRule,
          runRunRule] := by
  show rule ∈ (fixedRules ++ [releaseRule]) ++ headedRoots ++
      (sharedRunRules ++ [runBetaRule, runReleaseRule, runRunRule]) ↔ _
  rw [List.mem_append, List.mem_append]
  exact or_assoc

theorem headedContained_typeNames :
    headedContained.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem headedContained_signatures :
    RewriteValidationCertificate.constructorSignatures headedContained =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem headedContained_labels :
    RewriteValidationCertificate.constructorLabels headedContained =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the presentation passes its row of the declaration
gate. -/
theorem headedContained_rewrites_checked :
    ∀ rewrite ∈ headedContained.rewrites,
      RewriteValidationCertificate.check headedContained rewrite = true := by
  intro rewrite member
  rw [headedContained_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      headedContained_typeNames, headedContained_signatures, headedContained_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, headedRootRule,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runBetaRule, runReleaseRule, runRunRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The presentation passes the declaration gate.** -/
theorem headedContained_validate : headedContained.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks (lang := headedContained)
    (RewriteValidationCertificate.validate_signature_of_same_data (left := containedRun) rfl rfl rfl contained_signature_valid) (by decide +kernel) headedContained_rewrites_checked

/-- The presentation, as a presentation. -/
def headedPresentation : ValidatedLanguageDef := ⟨headedContained, headedContained_validate⟩

/-- **It differs from the contained presentation by its root steps alone**:
the same constructors, the same equation, and the eighteen rewrites of the
contained presentation other than the ambient root step. -/
theorem headedContained_differs :
    headedContained.terms = containedRun.terms ∧
      headedContained.equations = containedRun.equations ∧
        (∀ rule ∈ containedRun.rewrites, rule ≠ rootRule → rule ∈ headedContained.rewrites) ∧
          rootRule.name ∉ headedContained.rewrites.map (·.name) := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  intro rule member other
  rw [contained_rewrites] at member
  rw [headedContained_rewrites]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

/-! ## Its static equivalence -/

/-- **The static equivalence is that of quotation and dropping.** -/
theorem headedContained_quoteDropOnly : QuoteDropOnly headedContained :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem headedContained_quoteDropSorted : QuoteDropSorted headedContained :=
  ⟨by decide, by decide⟩

theorem headedContained_carriesAtoms : CarriesAtoms headedContained := by
  unfold CarriesAtoms
  decide

theorem headedContained_declaresRun : DeclaresRun headedContained := by
  unfold DeclaresRun
  decide

theorem headedContained_namesOnlyDropped : NamesOnlyDropped headedContained unquotedSorts :=
  atomsReduce_namesOnlyDropped

/-! ## The evaluator is the evaluator of a region, unchanged -/

/-- **The evaluator of a region respects the static equivalence** in every
language whose static equivalence is that of quotation and dropping and whose
premises are a query of the ambient root step for a first-order subject, the
premise of the root step of a run, or congruences. -/
theorem regionEvaluator_respectsStatics_of_queries {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (premises : ∀ premise ∈ presentedPremises lang,
      (∃ subject, isMatchCorrectAux subject = true ∧
        premise = .relationQuery "AmbientStep" [subject, .fvar "answer"]) ∨
      premise = runPremise ∨ ∃ source target, premise = .congruence source target)
    (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (only.equiv equivalent).1
  rcases premises premise member with ⟨subject, exact, rfl⟩ | rfl | ⟨source, target, rfl⟩
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
        (applyBindings first (.fvar "subject"))).map fun answer => ("answer", answer) :: first :=
      answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [admittedAnswers_congr admits
      (contract_applyBindings_congr contractions (.fvar "space") rfl)
      (contract_applyBindings_congr contractions (.fvar "subject") rfl)] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (admittedAnswers admits (applyBindings second (.fvar "space"))
      (applyBindings second (.fvar "subject"))).map fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [regionEvaluator] at answered

/-- **What the evaluator answers to a query of the ambient root step for any
subject pattern**: the answers of the ambient space for the instance of the
subject.  The eight root steps ask such queries; the evaluator is not
changed for them. -/
theorem regionEvaluator_ambientQuery (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang : LanguageDef) (bindings : Bindings) (subject : Pattern) :
    regionEvaluator admits ambientSpace lang bindings
        (.relationQuery "AmbientStep" [subject, .fvar "answer"]) =
      (admittedAnswers admits ambientSpace (applyBindings bindings subject)).map
        fun result => ("answer", result) :: bindings :=
  rfl

/-- The premises that the presentation hands to its evaluator. -/
theorem headedContained_premises : ∀ premise ∈ presentedPremises headedContained,
    (∃ subject, isMatchCorrectAux subject = true ∧
      premise = .relationQuery "AmbientStep" [subject, .fvar "answer"]) ∨
    premise = runPremise ∨ ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      [.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
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
        runPremise,
        .congruence (runPattern (.fvar "space") (.fvar "F")) (runPattern (.fvar "space") (.fvar "G")),
        .congruence (runPattern (.fvar "space") (.fvar "X")) (runPattern (.fvar "space") (.fvar "Y")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (runPattern (.fvar "space") (.fvar "X"))
          (runPattern (.fvar "space") (.fvar "Y"))] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inr (.inr ⟨_, _, rfl⟩)
    | exact .inr (.inl rfl)
    | exact .inl ⟨_, by decide, rfl⟩

/-- **Every member respects the static equivalence of the presentation**,
under every guard. -/
theorem headedContained_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) headedContained :=
  regionEvaluator_respectsStatics_of_queries headedContained_quoteDropOnly
    headedContained_premises admits ambientSpace

/-- A space of the presentation. -/
abbrev HeadedSpace : Type := Contexts.Term headedContained closedSpace

/-- **The member of the family at an ambient space**, as a presented
candidate: the presentation under the evaluator of a region. -/
def headedMember (admits : Pattern → Bool) (space : HeadedSpace) : PresentedCandidate where
  presentation := headedPresentation
  evaluator := regionEvaluator admits space.1
  respects := headedContained_respectsStatics admits space.1

/-- The theory of the presentation at an ambient space, with all its
contexts. -/
abbrev headedTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) headedPresentation

/-! ## A root step by one of the eight, on patterns -/

variable {lang : LanguageDef} {admits : Pattern → Bool} {ambientSpace : Pattern}

/-- **A headed root step**: from a pattern that the left side matches to an
answer of the ambient space for it that the guard admitted. -/
theorem step_headedRoot {name : String} {left : Pattern}
    (member : headedRootRule name left ∈ lang.rewrites) {subject answer : Pattern}
    {initial : Bindings} (matched : initial ∈ matchPattern left subject)
    (rebuilt : applyBindings initial left = subject)
    (found : answer ∈ admittedAnswers admits ambientSpace subject) :
    StepAt (regionEvaluator admits ambientSpace) lang 1 subject answer := by
  refine stepAt_of_rule (rule := headedRootRule name left) member (initial := initial)
    (final := ("answer", answer) :: initial) matched ?_ ?_
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (admittedAnswers admits ambientSpace (applyBindings initial left)).map
      fun result => ("answer", result) :: initial
    rw [rebuilt]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · show applyBindingsScoped left (("answer", answer) :: initial) 0 (.fvar "answer") = answer
    rw [applyBindingsScoped_fvar_zero]
    simp [applyBindings]

/-- What a headed root step is: an answer of the ambient space for the
source. -/
theorem headedRoot_inv {name : String} {left : Pattern} (exact : isMatchCorrectAux left = true)
    {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern (headedRootRule name left).left source)
    (premises : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      (headedRootRule name left).premises final) :
    ∃ answer, answer ∈ admittedAnswers admits ambientSpace source ∧
      applyRuleBindings (headedRootRule name left) final = answer := by
  have rebuilt : applyBindings initial left = source := matchPattern_correct matched exact
  have premises' : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      [.relationQuery "AmbientStep" [left, .fvar "answer"]] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (admittedAnswers admits ambientSpace
              (applyBindings initial left)).map fun result => ("answer", result) :: initial :=
            answered
          rw [rebuilt] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          refine ⟨answer, found, ?_⟩
          show applyBindingsScoped left (("answer", answer) :: initial) 0 (.fvar "answer") = answer
          rw [applyBindingsScoped_fvar_zero]
          simp [applyBindings]

/-- **Negative**: no headed root step matches a bound variable. -/
theorem headedRoots_not_matched_bvar {rule : RewriteRule} (member : rule ∈ headedRoots)
    {index : Nat} {bindings : Bindings} : bindings ∉ matchPattern rule.left (.bvar index) := by
  obtain ⟨name, label, parameters, rfl, -, -⟩ := headedRoots_shape rule member
  exact bvar_not_matched

/-- **Negative**: no headed root step matches a run. -/
theorem headedRoots_not_matched_run {rule : RewriteRule} (member : rule ∈ headedRoots)
    {space subject : Pattern} {bindings : Bindings} :
    bindings ∉ matchPattern rule.left (runPattern space subject) := by
  obtain ⟨name, label, parameters, rfl, -, listed⟩ := headedRoots_shape rule member
  refine run_not_matched (label := label) ?_
  rintro rfl
  exact absurd listed (by decide)

#print axioms headedRoots_shape
#print axioms headedContained_validate
#print axioms headedContained_differs
#print axioms headedContained_quoteDropOnly
#print axioms regionEvaluator_respectsStatics_of_queries
#print axioms regionEvaluator_ambientQuery
#print axioms headedContained_respectsStatics
#print axioms headedMember
#print axioms step_headedRoot
#print axioms headedRoot_inv
#print axioms headedRoots_not_matched_bvar
#print axioms headedRoots_not_matched_run
#print axioms atomRootHeads_cover
#print axioms atomRootHeads_exclude
#print axioms headedContained_rewrites
#print axioms mem_headedContained_rewrites
#print axioms headedContained_typeNames
#print axioms headedContained_signatures
#print axioms headedContained_labels
#print axioms headedContained_rewrites_checked
#print axioms headedContained_quoteDropSorted
#print axioms headedContained_carriesAtoms
#print axioms headedContained_declaresRun
#print axioms headedContained_namesOnlyDropped
#print axioms headedContained_premises

end Mettapedia.Logic.HostingStyles.AmbientRegions
