import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AtomsReduce.Language

/-!
# The ambient space: one presentation, and a family of evaluators indexed by a space

The candidate in which atoms reduce (`atomsReduce`) carries its space in a
run at the root of a term.  This module writes the same candidate with the
space outside the term.

## The presentation

`ambient` has the sorts and the constructors of `atomsReduce` except the run
constructor (`ambient_terms`), its one equation, and nine rewrites
(`ambient_rewrites`):

* beta and the six congruences of application, product and abstraction, and
  the release of a dropped quotation: the rewrites of `atomsReduce` whose left
  side is no run (`ambient_keeps`);
* **one rewrite for the root step of an atom**, `rootRule`:
  `AmbientStep(subject, answer) ⊢ subject ~> answer`.  Its premise is answered
  by the evaluator.

It has no run constructor, and none of the eight rewrites of `atomsReduce`
that are about a run (`ambient_leaves`): no rewrite hands a space down.

## The family

`ambientEvaluator space` answers the premise of the root step with the
answers of `space` for the subject, both read up to the static equivalence:
it is the matching evaluator with its space fixed
(`matchingEvaluator_run_eq_ambient`).  The index is a term of the candidate
of sort `Space` (`SpaceTerm`), so the rules are data; the space is the
parameter of the evaluator and the argument of no constructor
(`space_taken_by_no_atom`).

Every member respects the static equivalence (`ambient_respectsStatics`), so
each member is a presented candidate (`ambientMember`).  At a space that
stores no atom a member answers nothing (`ambientEvaluator_of_stores_nothing`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

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
open Mettapedia.Logic.HostingStyles.AtomsReduce

/-! ## The root step of an atom -/

/-- The premise of the root step: what the subject steps to.  The evaluator
answers it; the space is no argument of it. -/
def rootPremise : Premise := .relationQuery "AmbientStep" [.fvar "subject", .fvar "answer"]

/-- **The root step of an atom**: `AmbientStep(subject, answer) ⊢ subject ~> answer`. -/
def rootRule : RewriteRule :=
  { name := "Root"
    typeContext := [("subject", .base "Atom"), ("answer", .base "Atom")]
    premises := [rootPremise]
    left := .fvar "subject"
    right := .fvar "answer" }

/-! ## The presentation -/

/-- **The candidate with an ambient space**: the candidate in which atoms
reduce, without the run constructor and without the rewrites about a run, and
with one rewrite for the root step of an atom. -/
def ambient : LanguageDef :=
  { name := "metta-prime-ambient-space"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := fixedRules ++ [releaseRule, rootRule] }

theorem ambient_rewrites : ambient.rewrites =
    [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
      lamBodyRule, releaseRule, rootRule] :=
  rfl

theorem ambient_typeNames : ambient.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem ambient_signatures :
    RewriteValidationCertificate.constructorSignatures ambient =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem ambient_labels :
    RewriteValidationCertificate.constructorLabels ambient =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the presentation passes its row of the declaration
gate. -/
theorem ambient_rewrites_checked :
    ∀ rewrite ∈ ambient.rewrites,
      RewriteValidationCertificate.check ambient rewrite = true := by
  intro rewrite member
  rw [ambient_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      ambient_typeNames, ambient_signatures, ambient_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, rootRule, rootPremise,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The presentation passes the declaration gate.** -/
theorem ambient_validate : ambient.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := ambient)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) ambient_rewrites_checked

/-- The candidate with an ambient space, as a presentation. -/
def ambientPresentation : ValidatedLanguageDef := ⟨ambient, ambient_validate⟩

/-! ## What it has of the candidate with a run, and what it leaves -/

/-- **Its constructors are those of the candidate with a run, without the
run.** -/
theorem ambient_terms :
    ambient.terms = atomsReduce.terms.filter fun rule => rule.label != "prime-run" := by
  decide

/-- **Negative**: the run is no constructor of it. -/
theorem run_not_ambient : "prime-run" ∉ ambient.terms.map (·.label) := by decide

/-- **It keeps the rewrites of the candidate with a run that are about no
run**: beta, the six congruences and the release. -/
theorem ambient_keeps :
    ∀ rule ∈ fixedRules ++ [releaseRule], rule ∈ atomsReduce.rewrites ∧ rule ∈ ambient.rewrites := by
  intro rule member
  have listed : rule ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, releaseRule] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [atomsReduce_rewrites], by simp [ambient_rewrites]⟩

/-- **The heads of its nine left sides.**  None is a run, and the left side
of the root step has no head: it is a variable, and matches every pattern. -/
theorem ambient_left_heads :
    ambient.rewrites.map (fun rule => head? rule.left) =
      [some "App", some "App", some "App", some "Pi", some "Pi", some "Lam", some "Lam",
        some "prime-drop", none] := by
  rfl

/-- **It leaves the eight rewrites that are about a run**: the congruence of
the subject of a run, the root step of a run and the six congruences beneath
a run are those whose left side is a run, and no rewrite of the ambient
presentation has such a left side. -/
theorem ambient_leaves :
    (atomsReduce.rewrites.filter fun rule => head? rule.left == some "prime-run").map (·.name) =
        ["RunSubject", "prime-run", "RunAppFunction", "RunAppArgument", "RunPiDomain", "RunPiBody",
          "RunLamDomain", "RunLamBody"] ∧
      (ambient.rewrites.filter fun rule => head? rule.left == some "prime-run") = [] := by
  constructor <;> rfl

/-- **A space is the argument of no constructor of atoms and of no
constructor of names**: only a space takes a space. -/
theorem space_taken_by_no_atom :
    ∀ rule ∈ ambient.terms, rule.category ≠ "Space" →
      ∀ parameter ∈ rule.params, parameter.typeExpr ≠ .base "Space" := by
  decide

/-- **Negative**: in the candidate with a run an atom takes a space. -/
theorem space_taken_by_run :
    runAtomConstructor ∈ atomsReduce.terms ∧ runAtomConstructor.category = "Atom" ∧
      TermParam.simple "space" (.base "Space") ∈ runAtomConstructor.params := by
  decide

/-! ## Its static equivalence -/

/-- **The static equivalence is that of quotation and dropping.** -/
theorem ambient_quoteDropOnly : QuoteDropOnly ambient :=
  ⟨rfl, by decide, by decide, by decide⟩

/-- Quotation takes an atom to a name and dropping takes a name. -/
theorem ambient_quoteDropSorted : QuoteDropSorted ambient := ⟨by decide, by decide⟩

/-! ## The family of evaluators -/

/-- **The evaluator at a space**: it answers the premise of the root step
with the answers of the space for the subject, both read up to the static
equivalence, and it answers no other premise. -/
def ambientEvaluator (space : Pattern) : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "AmbientStep" [subject, .fvar answer] =>
      (matchResults (contract space) (contract (applyBindings bindings subject))).map
        fun result => (answer, result) :: bindings
  | _ => []

/-- What the evaluator at a space answers to the premise of the root step. -/
theorem ambientEvaluator_rootPremise (space : Pattern) (lang : LanguageDef) (bindings : Bindings) :
    ambientEvaluator space lang bindings rootPremise =
      (matchResults (contract space) (contract (applyBindings bindings (.fvar "subject")))).map
        fun result => ("answer", result) :: bindings :=
  rfl

/-- **The evaluator at a space is the matching evaluator with its space
fixed**: the matching evaluator answers the run premise as the member at the
space that the run binds answers the premise of the root step. -/
theorem matchingEvaluator_run_eq_ambient (lang : LanguageDef) (bindings : Bindings) :
    matchingEvaluator lang bindings runPremise =
      ambientEvaluator (applyBindings bindings (.fvar "space")) lang bindings rootPremise :=
  rfl

/-- **The evaluator reads its space up to the static equivalence**: two
spellings of one space give one evaluator. -/
theorem ambientEvaluator_congr {first second : Pattern} (same : contract first = contract second) :
    ambientEvaluator first = ambientEvaluator second := by
  funext lang bindings premise
  unfold ambientEvaluator
  rw [same]

/-- **Negative**: where the space stores no atom the evaluator answers
nothing, whatever the premise. -/
theorem ambientEvaluator_of_stores_nothing {space : Pattern}
    (empty : storedAtoms (contract space) = []) (lang : LanguageDef) (bindings : Bindings)
    (premise : Premise) : ambientEvaluator space lang bindings premise = [] := by
  unfold ambientEvaluator
  split
  · rw [matchResults, empty]
    rfl
  · rfl

/-- The premises that the presentation hands to its evaluator: the premise of
the root step, and congruences. -/
theorem ambient_premises : ∀ premise ∈ presentedPremises ambient,
    premise = rootPremise ∨ ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      [.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        rootPremise] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inr ⟨_, _, rfl⟩
    | exact .inl rfl

/-- **The evaluator at a space respects the static equivalence**, in every
language whose static equivalence is that of quotation and dropping and whose
premises are the premise of the root step or congruences. -/
theorem ambientEvaluator_respectsStatics_of_premises {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (premises : ∀ premise ∈ presentedPremises lang,
      premise = rootPremise ∨ ∃ source target, premise = .congruence source target)
    (space : Pattern) : RespectsStatics (ambientEvaluator space) lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (only.equiv equivalent).1
  rcases premises premise member with rfl | ⟨source, target, rfl⟩
  · have answers : result ∈ (matchResults (contract space)
        (contract (applyBindings first (.fvar "subject")))).map
          fun answer => ("answer", answer) :: first := answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [contract_applyBindings_congr contractions (.fvar "subject") rfl] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (matchResults (contract space)
      (contract (applyBindings second (.fvar "subject")))).map
        fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [ambientEvaluator] at answered

/-- **Every member of the family respects the static equivalence of the
presentation.** -/
theorem ambient_respectsStatics (space : Pattern) : RespectsStatics (ambientEvaluator space) ambient :=
  ambientEvaluator_respectsStatics_of_premises ambient_quoteDropOnly ambient_premises space

/-! ## The members -/

/-- **A space of the candidate**: a closed term of its sort `Space`.  The
index of the family. -/
abbrev SpaceTerm : Type := Contexts.Term ambient closedSpace

/-- **The member of the family at a space**, as a presented candidate: the
one presentation, under the evaluator that matches in that space. -/
def ambientMember (space : SpaceTerm) : PresentedCandidate where
  presentation := ambientPresentation
  evaluator := ambientEvaluator space.1
  respects := ambient_respectsStatics space.1

/-- The theory of the member at a space, with all its contexts. -/
abbrev ambientTheory (space : SpaceTerm) : ContextTheory.{0} :=
  contextTheory (ambientEvaluator space.1) ambientPresentation

theorem ambientMember_theory (space : SpaceTerm) : (ambientMember space).theory = ambientTheory space :=
  rfl

/-- All members have one presentation; they differ by their evaluator. -/
theorem ambientMember_presentation (first second : SpaceTerm) :
    (ambientMember first).presentation = (ambientMember second).presentation :=
  rfl

/-- The empty space, as a space of the candidate. -/
def emptySpaceTerm : SpaceTerm :=
  ⟨emptySpace, wellSorted_apply_zero (lang := ambient) (label := "prime-space-empty") (by decide)⟩

#print axioms ambient_validate
#print axioms ambient_terms
#print axioms ambient_keeps
#print axioms ambient_leaves
#print axioms space_taken_by_no_atom
#print axioms ambient_quoteDropOnly
#print axioms ambient_quoteDropSorted
#print axioms ambientEvaluator
#print axioms matchingEvaluator_run_eq_ambient
#print axioms ambientEvaluator_congr
#print axioms ambientEvaluator_of_stores_nothing
#print axioms ambient_premises
#print axioms ambientEvaluator_respectsStatics_of_premises
#print axioms ambient_respectsStatics
#print axioms ambientMember

end Mettapedia.Logic.HostingStyles.AmbientSpace
