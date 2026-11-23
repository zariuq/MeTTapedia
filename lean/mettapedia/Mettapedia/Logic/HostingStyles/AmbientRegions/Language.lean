import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AmbientSpace.Tokens

/-!
# The ambient space with a run as a region: two presentations and one family of evaluators

The candidate with an ambient space (`ambient`) has its space outside every
term; the candidate in which atoms reduce (`atomsReduce`) has it in a run.
This module puts the run constructor of sort `Atom` into the ambient
presentation, twice, and adds no equation.

## The two presentations

Both have the twelve constructors of `atomsReduce`, the one equation of
quotation and dropping, the nine rewrites of `ambient`, the root step of a
run and the six congruences beneath a run.  They differ by what else steps
beneath a run:

* `containedRun`: beta beneath a run (`runBetaRule`), the release of a dropped
  quotation beneath a run (`runReleaseRule`), and the step of a run beneath a
  run (`runRunRule`).  None of them has a plain step of the subject as its
  premise.
* `scopedRun`: the congruence of the subject of a run (`runSubjectRule`), whose
  premise is a plain step of the subject.

`contained_scoped_common`, `contained_alone` and `scoped_alone` list the
sixteen common rewrites and the four that differ.

## The family of evaluators

`regionEvaluator admits ambientSpace` answers the premise of the ambient root
step with the answers of `ambientSpace` for the subject, and the premise of
the root step of a run with the answers of the space of the run, both read
up to the static equivalence (`admittedAnswers`).  The guard `admits` says
for which subjects it answers; `anySubject` is no guard, and then the
evaluator is the evaluator of the ambient family on the first premise and the
matching evaluator on the second (`regionEvaluator_rootPremise_any`,
`regionEvaluator_runPremise_any`).

Every member respects the static equivalence of both presentations
(`contained_respectsStatics`, `scoped_respectsStatics`), under every guard, so
each presentation with each guard is a family of presented candidates indexed
by the ambient space (`containedMember`, `scopedMember`).
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
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace

/-! ## Three rewrites beneath a run that ask no plain step -/

/-- **Beta beneath a run**: `run(space, App(Lam(A, x. B), X)) ~> run(space, B[X/x])`. -/
def runBetaRule : RewriteRule :=
  { name := "RunBeta"
    typeContext := []
    premises := []
    left := runPattern (.fvar "space") betaLeft
    right := runPattern (.fvar "space") (.subst (.fvar "B") (.fvar "X")) }

/-- **The release of a dropped quotation beneath a run**:
`run(space, drop(quote(atom))) ~> run(space, atom)`. -/
def runReleaseRule : RewriteRule :=
  { name := "RunRelease"
    typeContext := [("space", .base "Space"), ("atom", .base "Atom")]
    premises := []
    left := runPattern (.fvar "space") (.apply "prime-drop" [.apply "prime-quote" [.fvar "atom"]])
    right := runPattern (.fvar "space") (.fvar "atom") }

/-- **The step of a run beneath a run**:
`run(space, X) ~> run(space, Y) ⊢ run(outer, run(space, X)) ~> run(outer, run(space, Y))`. -/
def runRunRule : RewriteRule :=
  { name := "RunRun"
    typeContext := []
    premises := [.congruence (runPattern (.fvar "space") (.fvar "X"))
      (runPattern (.fvar "space") (.fvar "Y"))]
    left := runPattern (.fvar "outer") (runPattern (.fvar "space") (.fvar "X"))
    right := runPattern (.fvar "outer") (runPattern (.fvar "space") (.fvar "Y")) }

/-- The rewrites about a run that both presentations have: the root step of a
run and the six congruences beneath a run. -/
def sharedRunRules : List RewriteRule := [runRewrite] ++ spatialCongruences

/-! ## The contained presentation -/

/-- **The ambient presentation with a contained run**: the constructors of
the candidate in which atoms reduce, the rewrites of the ambient
presentation, the root step of a run, the six congruences beneath a run, and
beta, release and the step of a run beneath a run. -/
def containedRun : LanguageDef :=
  { name := "metta-prime-ambient-space-contained-run"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := ambient.rewrites ++ sharedRunRules ++ [runBetaRule, runReleaseRule, runRunRule] }

theorem contained_rewrites : containedRun.rewrites =
    [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
      lamBodyRule, releaseRule, rootRule, runRewrite, runAppFunctionRule, runAppArgumentRule,
      runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule, runBetaRule,
      runReleaseRule, runRunRule] :=
  rfl

theorem contained_typeNames : containedRun.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem contained_signatures :
    RewriteValidationCertificate.constructorSignatures containedRun =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem contained_labels :
    RewriteValidationCertificate.constructorLabels containedRun =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the contained presentation passes its row of the
declaration gate. -/
theorem contained_rewrites_checked :
    ∀ rewrite ∈ containedRun.rewrites,
      RewriteValidationCertificate.check containedRun rewrite = true := by
  intro rewrite member
  rw [contained_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      contained_typeNames, contained_signatures, contained_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, rootRule, rootPremise,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runBetaRule, runReleaseRule, runRunRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- The contained, scoped, and headed variants share these static declarations. -/
theorem contained_signature_valid :
    ({ containedRun with rewrites := [] } : LanguageDef).validate = [] := by
  exact RewriteValidationCertificate.validate_signature_of_plain_equations (lang := containedRun)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The contained presentation passes the declaration gate.** -/
theorem contained_validate : containedRun.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks (lang := containedRun)
    contained_signature_valid (by decide +kernel) contained_rewrites_checked

/-- The contained presentation, as a presentation. -/
def containedPresentation : ValidatedLanguageDef := ⟨containedRun, contained_validate⟩

/-! ## The scoped presentation -/

/-- **The ambient presentation with a scoped run**: the constructors of the
candidate in which atoms reduce, the rewrites of the ambient presentation, and
the eight rewrites of that candidate about a run. -/
def scopedRun : LanguageDef :=
  { name := "metta-prime-ambient-space-scoped-run"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := ambient.rewrites ++ sharedRunRules ++ [runSubjectRule] }

theorem scoped_rewrites : scopedRun.rewrites =
    [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
      lamBodyRule, releaseRule, rootRule, runRewrite, runAppFunctionRule, runAppArgumentRule,
      runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule, runSubjectRule] :=
  rfl

theorem scoped_typeNames : scopedRun.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem scoped_signatures :
    RewriteValidationCertificate.constructorSignatures scopedRun =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem scoped_labels :
    RewriteValidationCertificate.constructorLabels scopedRun =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the scoped presentation passes its row of the
declaration gate. -/
theorem scoped_rewrites_checked :
    ∀ rewrite ∈ scopedRun.rewrites,
      RewriteValidationCertificate.check scopedRun rewrite = true := by
  intro rewrite member
  rw [scoped_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
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
      scoped_typeNames, scoped_signatures, scoped_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, rootRule, rootPremise,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runSubjectRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The scoped presentation passes the declaration gate.** -/
theorem scoped_validate : scopedRun.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks (lang := scopedRun)
    (RewriteValidationCertificate.validate_signature_of_same_data (left := containedRun) rfl rfl rfl contained_signature_valid) (by decide +kernel) scoped_rewrites_checked

/-- The scoped presentation, as a presentation. -/
def scopedPresentation : ValidatedLanguageDef := ⟨scopedRun, scoped_validate⟩

/-! ## What the two have in common, and which rewrites differ -/

/-- **Both have the constructors of the candidate in which atoms reduce**: the
constructors of the ambient presentation and the run. -/
theorem region_terms :
    containedRun.terms = atomsReduce.terms ∧ scopedRun.terms = atomsReduce.terms :=
  ⟨rfl, rfl⟩

/-- **Positive**: the run is a constructor of atoms of both. -/
theorem run_constructor_of_both :
    runAtomConstructor ∈ containedRun.terms ∧ runAtomConstructor ∈ scopedRun.terms ∧
      runAtomConstructor.category = "Atom" := by
  decide

/-- **Negative**: neither has a constructor that the candidate in which atoms
reduce does not have; in particular neither has a constructor that joins two
spaces. -/
theorem region_no_new_constructor :
    (∀ rule ∈ containedRun.terms, rule ∈ atomsReduce.terms) ∧
      ∀ rule ∈ scopedRun.terms, rule ∈ atomsReduce.terms :=
  ⟨fun _ member => member, fun _ member => member⟩

/-- **The sixteen rewrites that the two presentations have in common**: the
nine of the ambient presentation, the root step of a run and the six
congruences beneath a run. -/
theorem contained_scoped_common :
    ∀ rule ∈ ambient.rewrites ++ sharedRunRules,
      rule ∈ containedRun.rewrites ∧ rule ∈ scopedRun.rewrites := by
  intro rule member
  exact ⟨List.mem_append_left _ member, List.mem_append_left _ member⟩

/-- **The rewrites that the contained presentation has alone**: beta, release
and the step of a run, each beneath a run. -/
theorem contained_alone :
    (containedRun.rewrites.map (·.name)).filter
        (fun name => !(scopedRun.rewrites.map (·.name)).contains name) =
      ["RunBeta", "RunRelease", "RunRun"] := by
  decide

/-- **The rewrite that the scoped presentation has alone**: the congruence of
the subject of a run. -/
theorem scoped_alone :
    (scopedRun.rewrites.map (·.name)).filter
        (fun name => !(containedRun.rewrites.map (·.name)).contains name) =
      ["RunSubject"] := by
  decide

/-- The rewrites of a presentation have pairwise different names, so the two
lists above are lists of rewrites. -/
theorem region_rewrite_names_nodup :
    (containedRun.rewrites.map (·.name)).Nodup ∧ (scopedRun.rewrites.map (·.name)).Nodup := by
  decide

/-- **The scoped presentation has the rewrites of the candidate in which
atoms reduce, and the ambient root step.** -/
theorem scoped_rewrites_atomsReduce :
    (∀ rule ∈ atomsReduce.rewrites, rule ∈ scopedRun.rewrites) ∧
      ∀ rule ∈ scopedRun.rewrites, rule ∈ atomsReduce.rewrites ∨ rule = rootRule := by
  constructor
  · intro rule member
    rw [atomsReduce_rewrites] at member
    rw [scoped_rewrites]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  · intro rule member
    rw [scoped_rewrites] at member
    rw [atomsReduce_rewrites]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto

/-- The rewrites of the ambient presentation are rewrites of both. -/
theorem ambient_rewrites_subset :
    (∀ rule ∈ ambient.rewrites, rule ∈ containedRun.rewrites) ∧
      ∀ rule ∈ ambient.rewrites, rule ∈ scopedRun.rewrites :=
  ⟨fun _ member => List.mem_append_left _ (List.mem_append_left _ member),
    fun _ member => List.mem_append_left _ (List.mem_append_left _ member)⟩

/-! ## The static equivalence stays that of quotation and dropping -/

/-- **The static equivalence of the contained presentation is that of
quotation and dropping**: no equation moves a run. -/
theorem contained_quoteDropOnly : QuoteDropOnly containedRun :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem contained_quoteDropSorted : QuoteDropSorted containedRun := ⟨by decide, by decide⟩

/-- **The static equivalence of the scoped presentation is that of quotation
and dropping.** -/
theorem scoped_quoteDropOnly : QuoteDropOnly scopedRun :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem scoped_quoteDropSorted : QuoteDropSorted scopedRun := ⟨by decide, by decide⟩

/-- **Positive**: both carry the atoms of λΠ terms and the spaces of rules. -/
theorem region_carriesAtoms : CarriesAtoms containedRun ∧ CarriesAtoms scopedRun := by
  unfold CarriesAtoms
  decide

/-! ## The guards: for which subjects an evaluator answers -/

/-- **No guard**: the evaluator answers for every subject. -/
def anySubject : Pattern → Bool := fun _ => true

/-- **The subject is no run.** -/
def notRun : Pattern → Bool
  | .apply label _ => !(label == "prime-run")
  | _ => true

/-- **The head of the subject is no constructor of spaces and no quotation**:
as far as its head says, the subject is an atom. -/
def atomHead : Pattern → Bool
  | .apply label _ =>
      !(label == "prime-space-empty" || label == "prime-space-add" || label == "prime-quote")
  | _ => true

/-- **The subject is an atom, as far as its head says, and no run.** -/
def atomNotRun (subject : Pattern) : Bool := atomHead subject && notRun subject

/-- **Positive**: an application is no run. -/
theorem notRun_application (function argument : Pattern) :
    notRun (.apply "App" [function, argument]) = true := by
  simp [notRun]

/-- **Negative**: a run is one. -/
theorem notRun_run (space subject : Pattern) : notRun (runPattern space subject) = false := by
  simp [notRun, runPattern]

/-- **Positive**: a run has the head of an atom, and so has a bound
variable. -/
theorem atomHead_run (space subject : Pattern) : atomHead (runPattern space subject) = true := by
  simp [atomHead, runPattern]

theorem atomHead_bvar (index : Nat) : atomHead (.bvar index) = true := rfl

/-- **Negative**: the empty space, a space with one more atom and a quotation
have not. -/
theorem atomHead_emptySpace : atomHead emptySpace = false := by decide

theorem atomHead_addAtom (atom space : Pattern) : atomHead (addAtom atom space) = false := by
  simp [atomHead, addAtom]

theorem atomHead_quoted (atom : Pattern) : atomHead (quoted atom) = false := by
  simp [atomHead, quoted]

theorem atomNotRun_run (space subject : Pattern) :
    atomNotRun (runPattern space subject) = false := by
  simp [atomNotRun, notRun_run]

/-! ## The family of evaluators -/

/-- **The answers of a space for a subject that the guard admits**: the
answers of the space for the subject, both read up to the static equivalence,
and nothing for a subject that the guard refuses. -/
def admittedAnswers (admits : Pattern → Bool) (space subject : Pattern) : List Pattern :=
  if admits (contract subject) then matchResults (contract space) (contract subject) else []

/-- **Positive**: without a guard they are the answers of the space. -/
theorem admittedAnswers_any (space subject : Pattern) :
    admittedAnswers anySubject space subject = matchResults (contract space) (contract subject) :=
  rfl

/-- **Negative**: nothing for a subject that the guard refuses. -/
theorem admittedAnswers_of_not_admitted {admits : Pattern → Bool} {subject : Pattern}
    (refused : admits (contract subject) = false) (space : Pattern) :
    admittedAnswers admits space subject = [] := by
  simp [admittedAnswers, refused]

theorem mem_admittedAnswers {admits : Pattern → Bool} {space subject answer : Pattern} :
    answer ∈ admittedAnswers admits space subject ↔
      admits (contract subject) = true ∧
        answer ∈ matchResults (contract space) (contract subject) := by
  unfold admittedAnswers
  split_ifs with admitted
  · exact ⟨fun found => ⟨admitted, found⟩, fun found => found.2⟩
  · exact ⟨fun found => absurd found List.not_mem_nil, fun found => absurd found.1 admitted⟩

/-- They read the space and the subject up to the static equivalence. -/
theorem admittedAnswers_congr (admits : Pattern → Bool) {space subject otherSpace otherSubject : Pattern}
    (spaces : contract space = contract otherSpace)
    (subjects : contract subject = contract otherSubject) :
    admittedAnswers admits space subject = admittedAnswers admits otherSpace otherSubject := by
  unfold admittedAnswers
  rw [spaces, subjects]

/-- The answers under a guard are answers without one. -/
theorem admittedAnswers_subset_any {admits : Pattern → Bool} {space subject answer : Pattern}
    (found : answer ∈ admittedAnswers admits space subject) :
    answer ∈ admittedAnswers anySubject space subject :=
  (mem_admittedAnswers.mp found).2

/-- **The evaluator of a region**, at an ambient space: it answers the premise
of the ambient root step with the answers of the ambient space, the premise
of the root step of a run with the answers of the space of the run, each for
the subjects that the guard admits, and it answers no other premise. -/
def regionEvaluator (admits : Pattern → Bool) (ambientSpace : Pattern) : BasePremiseEvaluator :=
  fun _ bindings premise =>
    match premise with
    | .relationQuery "AmbientStep" [subject, .fvar answer] =>
        (admittedAnswers admits ambientSpace (applyBindings bindings subject)).map
          fun result => (answer, result) :: bindings
    | .relationQuery "PrimeStep" [space, subject, .fvar answer] =>
        (admittedAnswers admits (applyBindings bindings space)
          (applyBindings bindings subject)).map fun result => (answer, result) :: bindings
    | _ => []

/-- What it answers to the premise of the ambient root step. -/
theorem regionEvaluator_rootPremise (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang : LanguageDef) (bindings : Bindings) :
    regionEvaluator admits ambientSpace lang bindings rootPremise =
      (admittedAnswers admits ambientSpace (applyBindings bindings (.fvar "subject"))).map
        fun result => ("answer", result) :: bindings :=
  rfl

/-- What it answers to the premise of the root step of a run. -/
theorem regionEvaluator_runPremise (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang : LanguageDef) (bindings : Bindings) :
    regionEvaluator admits ambientSpace lang bindings runPremise =
      (admittedAnswers admits (applyBindings bindings (.fvar "space"))
        (applyBindings bindings (.fvar "subject"))).map
          fun result => ("answer", result) :: bindings :=
  rfl

/-- **Without a guard it answers the ambient root step as the member of the
ambient family at the ambient space does.** -/
theorem regionEvaluator_rootPremise_any (ambientSpace : Pattern) (lang : LanguageDef)
    (bindings : Bindings) :
    regionEvaluator anySubject ambientSpace lang bindings rootPremise =
      ambientEvaluator ambientSpace lang bindings rootPremise :=
  rfl

/-- **Without a guard it answers the root step of a run as the matching
evaluator does**: from the space of the run, whatever the ambient space is. -/
theorem regionEvaluator_runPremise_any (ambientSpace : Pattern) (lang : LanguageDef)
    (bindings : Bindings) :
    regionEvaluator anySubject ambientSpace lang bindings runPremise =
      matchingEvaluator lang bindings runPremise :=
  rfl

/-- **Negative**: it answers no congruence premise. -/
theorem regionEvaluator_congruence (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang : LanguageDef) (bindings : Bindings) (source target : Pattern) :
    regionEvaluator admits ambientSpace lang bindings (.congruence source target) = [] :=
  rfl

/-- **The evaluator reads its ambient space up to the static equivalence.** -/
theorem regionEvaluator_congr (admits : Pattern → Bool) {first second : Pattern}
    (same : contract first = contract second) :
    regionEvaluator admits first = regionEvaluator admits second := by
  funext lang bindings premise
  unfold regionEvaluator
  split
  · rw [admittedAnswers_congr admits same rfl]
  · rfl
  · rfl

/-- **The answer to the root step of a run does not mention the ambient
space.** -/
theorem regionEvaluator_runPremise_ambient_irrelevant (admits : Pattern → Bool)
    (first second : Pattern) (lang : LanguageDef) (bindings : Bindings) :
    regionEvaluator admits first lang bindings runPremise =
      regionEvaluator admits second lang bindings runPremise :=
  rfl

/-! ## Every member respects the static equivalence -/

/-- **The evaluator of a region respects the static equivalence**, under every
guard and at every ambient space, in every language whose static equivalence
is that of quotation and dropping and whose premises are the premise of the
ambient root step, the premise of the root step of a run, or congruences. -/
theorem regionEvaluator_respectsStatics_of_premises {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (premises : ∀ premise ∈ presentedPremises lang,
      premise = rootPremise ∨ premise = runPremise ∨
        ∃ source target, premise = .congruence source target)
    (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (only.equiv equivalent).1
  rcases premises premise member with rfl | rfl | ⟨source, target, rfl⟩
  · have answers : result ∈ (admittedAnswers admits ambientSpace
        (applyBindings first (.fvar "subject"))).map fun answer => ("answer", answer) :: first :=
      answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [admittedAnswers_congr admits rfl
      (contract_applyBindings_congr contractions (.fvar "subject") rfl)] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (admittedAnswers admits ambientSpace
      (applyBindings second (.fvar "subject"))).map fun answer => ("answer", answer) :: second
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

/-- The premises that the contained presentation hands to its evaluator. -/
theorem contained_premises : ∀ premise ∈ presentedPremises containedRun,
    premise = rootPremise ∨ premise = runPremise ∨
      ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      [.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        rootPremise, runPremise,
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
    rfl | rfl
  all_goals first
    | exact .inr (.inr ⟨_, _, rfl⟩)
    | exact .inl rfl
    | exact .inr (.inl rfl)

/-- The premises that the scoped presentation hands to its evaluator. -/
theorem scoped_premises : ∀ premise ∈ presentedPremises scopedRun,
    premise = rootPremise ∨ premise = runPremise ∨
      ∃ source target, premise = .congruence source target := by
  intro premise member
  have listed : premise ∈
      [.congruence (.fvar "F") (.fvar "G"), .congruence (.fvar "X") (.fvar "Y"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        .congruence (.fvar "A") (.fvar "C"), .congruence (.fvar "B") (.fvar "D"),
        rootPremise, runPremise,
        .congruence (runPattern (.fvar "space") (.fvar "F")) (runPattern (.fvar "space") (.fvar "G")),
        .congruence (runPattern (.fvar "space") (.fvar "X")) (runPattern (.fvar "space") (.fvar "Y")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (runPattern (.fvar "space") (.fvar "A")) (runPattern (.fvar "space") (.fvar "C")),
        .congruence (runPattern (.fvar "space") (.fvar "B")) (runPattern (.fvar "space") (.fvar "D")),
        .congruence (.fvar "X") (.fvar "Y")] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact .inr (.inr ⟨_, _, rfl⟩)
    | exact .inl rfl
    | exact .inr (.inl rfl)

/-- **Every member respects the static equivalence of the contained
presentation**, under every guard. -/
theorem contained_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) containedRun :=
  regionEvaluator_respectsStatics_of_premises contained_quoteDropOnly contained_premises admits
    ambientSpace

/-- **Every member respects the static equivalence of the scoped
presentation**, under every guard. -/
theorem scoped_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) scopedRun :=
  regionEvaluator_respectsStatics_of_premises scoped_quoteDropOnly scoped_premises admits
    ambientSpace

/-- It respects the static equivalence of the ambient presentation too. -/
theorem ambient_respectsStatics_region (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) ambient :=
  regionEvaluator_respectsStatics_of_premises ambient_quoteDropOnly
    (fun premise member => (ambient_premises premise member).elim .inl fun other => .inr (.inr other))
    admits ambientSpace

/-! ## The members -/

/-- A space of the contained presentation: a closed term of its sort
`Space`.  It may store atoms with runs. -/
abbrev ContainedSpace : Type := Contexts.Term containedRun closedSpace

/-- A space of the scoped presentation. -/
abbrev ScopedSpace : Type := Contexts.Term scopedRun closedSpace

/-- **The member of the contained family at an ambient space**, under a
guard, as a presented candidate. -/
def containedMember (admits : Pattern → Bool) (space : ContainedSpace) : PresentedCandidate where
  presentation := containedPresentation
  evaluator := regionEvaluator admits space.1
  respects := contained_respectsStatics admits space.1

/-- **The member of the scoped family at an ambient space**, under a guard,
as a presented candidate. -/
def scopedMember (admits : Pattern → Bool) (space : ScopedSpace) : PresentedCandidate where
  presentation := scopedPresentation
  evaluator := regionEvaluator admits space.1
  respects := scoped_respectsStatics admits space.1

/-- The theory of the contained presentation at an ambient space, with all
its contexts. -/
abbrev containedTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) containedPresentation

/-- The theory of the scoped presentation at an ambient space, with all its
contexts. -/
abbrev scopedTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) scopedPresentation

theorem containedMember_theory (admits : Pattern → Bool) (space : ContainedSpace) :
    (containedMember admits space).theory = containedTheory admits space.1 :=
  rfl

theorem scopedMember_theory (admits : Pattern → Bool) (space : ScopedSpace) :
    (scopedMember admits space).theory = scopedTheory admits space.1 :=
  rfl

/-- All members of one family have one presentation; they differ by their
evaluator. -/
theorem containedMember_presentation (admits : Pattern → Bool) (first second : ContainedSpace) :
    (containedMember admits first).presentation = (containedMember admits second).presentation :=
  rfl

/-- A space of the ambient presentation, as a space of the contained one. -/
def containedSpaceOf (space : SpaceTerm) : ContainedSpace :=
  ⟨space.1, wellSorted_of_terms_subset (small := ambient) (large := containedRun) (by decide) space.2⟩

/-- A space of the ambient presentation, as a space of the scoped one. -/
def scopedSpaceOf (space : SpaceTerm) : ScopedSpace :=
  ⟨space.1, wellSorted_of_terms_subset (small := ambient) (large := scopedRun) (by decide) space.2⟩

#print axioms contained_validate
#print axioms scoped_validate
#print axioms contained_scoped_common
#print axioms contained_alone
#print axioms scoped_alone
#print axioms scoped_rewrites_atomsReduce
#print axioms contained_quoteDropOnly
#print axioms scoped_quoteDropOnly
#print axioms regionEvaluator
#print axioms regionEvaluator_rootPremise_any
#print axioms regionEvaluator_runPremise_any
#print axioms regionEvaluator_congr
#print axioms regionEvaluator_respectsStatics_of_premises
#print axioms contained_respectsStatics
#print axioms scoped_respectsStatics
#print axioms containedMember
#print axioms scopedMember
#print axioms contained_rewrites
#print axioms contained_typeNames
#print axioms contained_signatures
#print axioms contained_labels
#print axioms contained_rewrites_checked
#print axioms scoped_rewrites
#print axioms scoped_typeNames
#print axioms scoped_signatures
#print axioms scoped_labels
#print axioms scoped_rewrites_checked
#print axioms region_terms
#print axioms run_constructor_of_both
#print axioms region_no_new_constructor
#print axioms region_rewrite_names_nodup
#print axioms ambient_rewrites_subset
#print axioms contained_quoteDropSorted
#print axioms scoped_quoteDropSorted
#print axioms region_carriesAtoms
#print axioms notRun_application
#print axioms notRun_run
#print axioms atomHead_run
#print axioms atomHead_bvar
#print axioms atomHead_emptySpace
#print axioms atomHead_addAtom
#print axioms atomHead_quoted
#print axioms atomNotRun_run
#print axioms admittedAnswers_any
#print axioms admittedAnswers_of_not_admitted
#print axioms mem_admittedAnswers
#print axioms admittedAnswers_congr
#print axioms admittedAnswers_subset_any
#print axioms regionEvaluator_rootPremise
#print axioms regionEvaluator_runPremise
#print axioms regionEvaluator_congruence
#print axioms regionEvaluator_runPremise_ambient_irrelevant
#print axioms contained_premises
#print axioms scoped_premises
#print axioms ambient_respectsStatics_region
#print axioms containedMember_theory
#print axioms scopedMember_theory
#print axioms containedMember_presentation

end Mettapedia.Logic.HostingStyles.AmbientRegions
