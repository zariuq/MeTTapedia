import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.PrimeCandidate.CandidateSentence

/-!
# A candidate in which atoms reduce

The candidate presentation (the probe) reduces in a sort of processes that no
constructor takes, and its header records that this contradicts the principle
*atoms reduce and data does not*.  This module writes a presentation that
follows the principle, `atomsReduce`, and names it as a presented candidate
under the matching evaluator, `atomsReduceProbe`.

## Sorts

`Atom`, `Space`, `CandidateName`.  There is no sort of processes: what
reduces is an atom.

## Constructors

| label | sort | arguments | from |
|---|---|---|---|
| `prime-unit` | `Atom` | | the probe |
| `=` | `Atom` | `Atom`, `Atom` | the probe: an equation, the form of a stored rule |
| `prime-quote` | `CandidateName` | `Atom` | the probe |
| `prime-drop` | `Atom` | `CandidateName` | the probe |
| `prime-space-empty` | `Space` | | the space extension of the probe |
| `prime-space-add` | `Space` | `Atom`, `Space` | the space extension |
| `prime-variable` | `Atom` | `Atom` | the space extension: a variable, named by an atom |
| `prime-symbol` | `Atom` | `Atom` | new: a symbol, named by an atom |
| `prime-run` | `Atom` | `Space`, `Atom` | the run constructor, here a constructor of atoms |
| `App` | `Atom` | `Atom`, `Atom` | new: expression formation, taking atoms |
| `Lam` | `Atom` | `Atom`, an atom beneath a binder | new: abstraction |
| `Pi` | `Atom` | `Atom`, an atom beneath a binder | new: product |

Left out of the probe: the sorts `Process`, `Alternatives` and
`CandidateReceipt`, and the constructors of the query and evaluation
machines, of Need requests, of dependency markers and of receipts
(`atomsReduce_leaves`).

## Equation

`prime-quote (prime-drop name) = name`, the equation of the probe.

## Rewrites

* On every atom: beta with a substitution node and the six congruences of
  application, product and abstraction (the rewrites of the language of the
  pure λΠ-calculus, `Dedukti.Language.fixedRules`); the release of a dropped
  quotation (`releaseRule`); and the congruence beneath a run
  (`runSubjectRule`).
* On a run: the root step, whose premise the evaluator answers from the space
  (`runRewrite`, the rewrite of the probe with a run constructor), and the six
  congruences beneath a run, whose premise is a step of the run of the part
  in the same space (`runAppFunctionRule` … `runLamBodyRule`).  This is how a
  part of an atom knows its space: the run constructor carries it.

There is no congruence beneath a quotation, a symbol, a variable, an equation
or a space: no left side is headed by one of them (`left_heads`), and neither
a name nor a space has a transition (`name_static`, `space_static`).

## What is proved here

* The presentation passes the declaration gate (`atomsReduce_validate`).
* Its static equivalence is that of quotation and dropping
  (`atomsReduce_quoteDropOnly`, `atomsReduce_quoteDropSorted`).
* The matching evaluator respects it (`atomsReduce_respectsStatics`), so the
  presentation under that evaluator is a presented candidate
  (`atomsReduceProbe`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

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
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## Constructors -/

/-- A symbol, named by an atom. -/
def symbolConstructor : GrammarRule :=
  plainConstructor "prime-symbol" "Atom" [.simple "index" (.base "Atom")]

/-- **The run of an atom in a space, as an atom.** -/
def runAtomConstructor : GrammarRule :=
  plainConstructor "prime-run" "Atom"
    [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")]

/-- The body of an abstraction or of a product: an atom beneath one binder of
an atom. -/
def atomBody : TermParam := .abstractionNamed (some "x") "body" (.base "Atom")

/-- **Expression formation**: the application of an atom to an atom. -/
def applicationConstructor : GrammarRule :=
  plainConstructor "App" "Atom" [.simple "f" (.base "Atom"), .simple "a" (.base "Atom")]

/-- Abstraction. -/
def abstractionConstructor : GrammarRule :=
  plainConstructor "Lam" "Atom" [.simple "a" (.base "Atom"), atomBody]

/-- Product. -/
def productConstructor : GrammarRule :=
  plainConstructor "Pi" "Atom" [.simple "a" (.base "Atom"), atomBody]

/-! ## Rewrites -/

/-- **Dropping a quotation releases the quoted atom.** -/
def releaseRule : RewriteRule :=
  { name := "Release"
    typeContext := [("atom", .base "Atom")]
    premises := []
    left := .apply "prime-drop" [.apply "prime-quote" [.fvar "atom"]]
    right := .fvar "atom" }

/-- **The congruence beneath a run**: `X ~> Y ⊢ run(space, X) ~> run(space, Y)`. -/
def runSubjectRule : RewriteRule :=
  { name := "RunSubject"
    typeContext := []
    premises := [.congruence (.fvar "X") (.fvar "Y")]
    left := runPattern (.fvar "space") (.fvar "X")
    right := runPattern (.fvar "space") (.fvar "Y") }

/-- `run(space, F) ~> run(space, G) ⊢ run(space, App(F, X)) ~> run(space, App(G, X))`. -/
def runAppFunctionRule : RewriteRule :=
  { name := "RunAppFunction"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "F"))
      (runPattern (.fvar "space") (.fvar "G"))]
    left := runPattern (.fvar "space") appLeft
    right := runPattern (.fvar "space") (.apply "App" [.fvar "G", .fvar "X"]) }

/-- `run(space, X) ~> run(space, Y) ⊢ run(space, App(F, X)) ~> run(space, App(F, Y))`. -/
def runAppArgumentRule : RewriteRule :=
  { name := "RunAppArgument"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "X"))
      (runPattern (.fvar "space") (.fvar "Y"))]
    left := runPattern (.fvar "space") appLeft
    right := runPattern (.fvar "space") (.apply "App" [.fvar "F", .fvar "Y"]) }

/-- `run(space, A) ~> run(space, C) ⊢ run(space, Pi(A, x. B)) ~> run(space, Pi(C, x. B))`. -/
def runPiDomainRule : RewriteRule :=
  { name := "RunPiDomain"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "A"))
      (runPattern (.fvar "space") (.fvar "C"))]
    left := runPattern (.fvar "space") piLeft
    right := runPattern (.fvar "space") (.apply "Pi" [.fvar "C", .lambda none (.fvar "B")]) }

/-- `run(space, B) ~> run(space, D) ⊢ run(space, Pi(A, x. B)) ~> run(space, Pi(A, x. D))`. -/
def runPiBodyRule : RewriteRule :=
  { name := "RunPiBody"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "B"))
      (runPattern (.fvar "space") (.fvar "D"))]
    left := runPattern (.fvar "space") piLeft
    right := runPattern (.fvar "space") (.apply "Pi" [.fvar "A", .lambda none (.fvar "D")]) }

/-- `run(space, A) ~> run(space, C) ⊢ run(space, Lam(A, x. B)) ~> run(space, Lam(C, x. B))`. -/
def runLamDomainRule : RewriteRule :=
  { name := "RunLamDomain"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "A"))
      (runPattern (.fvar "space") (.fvar "C"))]
    left := runPattern (.fvar "space") lamLeft
    right := runPattern (.fvar "space") (.apply "Lam" [.fvar "C", .lambda none (.fvar "B")]) }

/-- `run(space, B) ~> run(space, D) ⊢ run(space, Lam(A, x. B)) ~> run(space, Lam(A, x. D))`. -/
def runLamBodyRule : RewriteRule :=
  { name := "RunLamBody"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "B"))
      (runPattern (.fvar "space") (.fvar "D"))]
    left := runPattern (.fvar "space") lamLeft
    right := runPattern (.fvar "space") (.apply "Lam" [.fvar "A", .lambda none (.fvar "D")]) }

/-- The rewrites of an atom that do not ask the space: beta, the six
congruences, the release of a dropped quotation and the congruence beneath a
run. -/
def plainRules : List RewriteRule := fixedRules ++ [releaseRule, runSubjectRule]

/-- The rewrites of a run that carry its space to a part: the six congruences
beneath a run. -/
def spatialCongruences : List RewriteRule :=
  [runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule,
    runLamBodyRule]

/-! ## The presentation -/

/-- **The candidate in which atoms reduce.** -/
def atomsReduce : LanguageDef :=
  { name := "metta-prime-atoms-reduce"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := plainRules ++ [runRewrite] ++ spatialCongruences }

theorem atomsReduce_rewrites : atomsReduce.rewrites =
    [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
      lamBodyRule, releaseRule, runSubjectRule, runRewrite, runAppFunctionRule,
      runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule] :=
  rfl

theorem atomsReduce_typeNames : atomsReduce.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem atomsReduce_signatures :
    RewriteValidationCertificate.constructorSignatures atomsReduce =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem atomsReduce_labels :
    RewriteValidationCertificate.constructorLabels atomsReduce =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the candidate passes its row of the declaration gate. -/
theorem atomsReduce_rewrites_checked :
    ∀ rewrite ∈ atomsReduce.rewrites,
      RewriteValidationCertificate.check atomsReduce rewrite = true := by
  intro rewrite member
  rw [atomsReduce_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
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
      atomsReduce_typeNames, atomsReduce_signatures, atomsReduce_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, runSubjectRule,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The candidate passes the declaration gate.** -/
theorem atomsReduce_validate : atomsReduce.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := atomsReduce)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) atomsReduce_rewrites_checked

/-- The candidate, as a presentation. -/
def atomsReducePresentation : ValidatedLanguageDef := ⟨atomsReduce, atomsReduce_validate⟩

/-! ## Its static equivalence -/

/-- **The static equivalence of the candidate is that of quotation and
dropping**: the equation of the probe is its one equation, and a space is no
bag. -/
theorem atomsReduce_quoteDropOnly : QuoteDropOnly atomsReduce :=
  ⟨rfl, by decide, by decide, by decide⟩

/-- Quotation takes an atom to a name and dropping takes a name, as in the
probe. -/
theorem atomsReduce_quoteDropSorted : QuoteDropSorted atomsReduce := ⟨by decide, by decide⟩

/-- **Negative**: the language of the pure λΠ-calculus has no equation. -/
theorem dkLanguage_not_quoteDropOnly :
    ¬ QuoteDropOnly (Mettapedia.GSLT.Dedukti.Language.dkLanguage [] []) :=
  fun only => List.cons_ne_nil _ _ only.equations.symm

/-! ## The evaluator -/

/-- The premises that the candidate hands to its evaluator are the run
premise and congruences. -/
theorem atomsReduce_premises : ∀ premise ∈ presentedPremises atomsReduce,
    premise ∈ presentedPremises probeWithRun ∨ ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      [.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "X") (.fvar "Y"), runPremise,
        .congruence (runPattern (.fvar "space") (.fvar "F")) (runPattern (.fvar "space") (.fvar "G")),
        .congruence (runPattern (.fvar "space") (.fvar "X")) (runPattern (.fvar "space") (.fvar "Y")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D"))] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals first
    | exact .inr ⟨_, _, rfl⟩
    | exact .inl (by rw [presentedPremises_probeWithRun]; simp)

/-- **The matching evaluator respects the static equivalence of the
candidate.** -/
theorem atomsReduce_respectsStatics : RespectsStatics matchingEvaluator atomsReduce :=
  matchingEvaluator_respectsStatics_of_premises atomsReduce_quoteDropOnly atomsReduce_premises

/-- **The candidate in which atoms reduce, as a presented candidate**: the
presentation under the matching evaluator. -/
def atomsReduceProbe : PresentedCandidate where
  presentation := atomsReducePresentation
  evaluator := matchingEvaluator
  respects := atomsReduce_respectsStatics

/-- The theory of the candidate, with all its contexts. -/
abbrev atomsReduceTheory : ContextTheory.{0} := contextTheory matchingEvaluator atomsReducePresentation

theorem atomsReduceProbe_theory : atomsReduceProbe.theory = atomsReduceTheory := rfl

/-! ## What is carried from the probe, and what is left -/

/-- **What the candidate carries from the probe with a space**: the equation
constructor, the unit atom, quotation, dropping, the two constructors of a
space and the variable atom, each as it is declared there. -/
theorem atomsReduce_carries :
    ∀ rule ∈ [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
      emptySpaceConstructor, addAtomConstructor, variableConstructor],
      rule ∈ probeWithSpace.terms ∧ rule ∈ atomsReduce.terms := by
  decide

/-- **What it leaves**: no constructor of the query and evaluation machines,
of Need requests, of dependency markers or of receipts, and none of the sorts
of processes, alternatives and receipts. -/
theorem atomsReduce_leaves :
    (∀ label ∈ ["zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
      "prime-evaluate-name", "prime-need", "prime-need-answer", "prime-need-key",
      "prime-request-dependency", "prime-space-atom-dependency", "prime-capability-dependency",
      "prime-inert-dependency", "prime-receipt"],
      label ∉ atomsReduce.terms.map (·.label)) ∧
    (∀ sort ∈ ["Process", "Alternatives", "CandidateReceipt"], sort ∉ atomsReduce.typeNames) := by
  decide

/-- **The run constructor is a constructor of atoms here**, and of processes
in the probe with a run constructor. -/
theorem runConstructor_sorts :
    runAtomConstructor.category = "Atom" ∧ runConstructor.category = "Process" ∧
      runAtomConstructor.label = runConstructor.label ∧
        runAtomConstructor.params = runConstructor.params := by
  decide

/-- **The rewrite of the root step is the run rewrite of the probe with a run
constructor**, and beta and the six congruences are those of the language of
the pure λΠ-calculus. -/
theorem atomsReduce_reuses :
    runRewrite ∈ atomsReduce.rewrites ∧ runRewrite ∈ probeWithRun.rewrites ∧
      (∀ rule ∈ fixedRules, rule ∈ atomsReduce.rewrites) ∧
        ∀ rule ∈ fixedRules,
          rule ∈ (Mettapedia.GSLT.Dedukti.Language.dkLanguage [] []).rewrites :=
  ⟨by simp [atomsReduce_rewrites], by simp [probeWithRun_rewrites],
    fun _ member =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)),
    fun _ member => List.mem_append_left _ member⟩

#print axioms atomsReduce_validate
#print axioms atomsReduce_quoteDropOnly
#print axioms atomsReduce_quoteDropSorted
#print axioms atomsReduce_premises
#print axioms atomsReduce_respectsStatics
#print axioms atomsReduceProbe
#print axioms atomsReduce_carries
#print axioms atomsReduce_leaves
#print axioms runConstructor_sorts
#print axioms atomsReduce_reuses

end Mettapedia.Logic.HostingStyles.AtomsReduce
