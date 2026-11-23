import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProbeData
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ChoiceExtension

/-!
# One constructor and one rewrite: hosting on terms is then the evaluator's

The rewrites of a presented language may carry premises that an evaluator
outside the language answers (`BasePremiseEvaluator`).  The probe has a rank
for every such evaluator.  This module adds to the probe one constructor of
processes and one rewrite on it whose premise is delegated,

    prime-run space subject  ⟶  prime-run space answer     if PrimeStep(space, subject, answer),

and shows what that single change does on terms.

* **For every finitely branching numbered theory there is an evaluator of
  the premises under which the extended presentation hosts it on terms**
  (`runMap_hosting`).  The theory is given by a `StepListing`: a number for
  each term and the list of the reducts of each term.  A term is read as
  `prime-run` of the numeral of its number; the evaluator
  (`stepEvaluator`) answers with the numerals of the reducts.
* **One evaluator serves a numbered family** of listed theories
  (`runPresentation_hosts_family`): the family is hosted through its union
  (`unionTheory`, `unionListing`), and the number of the member is carried
  inside the term.
* So under such an evaluator the extended presentation has reductions of
  every length and cyclic reductions (`run_steps`, `run_not_rank`).
* **Under the evaluator that answers nothing it has a rank**
  (`silentRunRank`), like the probe.
* Its contexts still have a linear size (`runLinearSize`): the change is
  about terms.

The evaluator of a listing reads its subject up to the static equivalence
(`stepAnswers_congr`).  The rule-table evaluator itself has no listing: under
a table with a rule whose right side is not determined by its left side one
term reduces to every term (`evaluatorTerms_not_listing`).  The theories given
by a table whose rules determine their right sides are listed
(`DeterminedTables`), and the rule-table evaluator is hosted by the same
presentation through an evaluator that reads the spelling of its subject
(`SpellingEvaluator`).

The hosting power on terms of a presentation with a delegated premise is the
power of its evaluator.  A hosting statement about such a candidate has to
say which evaluator it is about.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## The extension -/

/-- A process that runs an atom in a space. -/
def runConstructor : GrammarRule :=
  { label := "prime-run"
    category := "Process"
    params := [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")]
    syntaxPattern := [] }

/-- **One step of running**: the premise is answered by the evaluator. -/
def runRewrite : RewriteRule :=
  { name := "prime-run"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom"), ("answer", .base "Atom")]
    premises := [.relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"]]
    left := .apply "prime-run" [.fvar "space", .fvar "subject"]
    right := .apply "prime-run" [.fvar "space", .fvar "answer"] }

/-- **The probe with a run constructor.** -/
def probeWithRun : LanguageDef :=
  { language with
    name := "metta-prime-spec-probe-with-run"
    terms := language.terms ++ [runConstructor]
    rewrites := language.rewrites ++ [runRewrite] }

theorem probeWithRun_typeNames : probeWithRun.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"] := by
  decide

theorem probeWithRun_signatures :
    RewriteValidationCertificate.constructorSignatures probeWithRun =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("prime-run", 2)] := by
  decide

theorem probeWithRun_labels :
    RewriteValidationCertificate.constructorLabels probeWithRun =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "prime-run"] := by
  decide

theorem probeWithRun_rewrites : probeWithRun.rewrites =
    [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite, needRewrite,
      needReturnRewrite, reflectedDemandRewrite, runRewrite] :=
  rfl

/-- Every rewrite of the extension passes its row of the declaration gate. -/
theorem probeWithRun_rewrites_checked :
    ∀ rewrite ∈ probeWithRun.rewrites,
      RewriteValidationCertificate.check probeWithRun rewrite = true := by
  intro rewrite member
  rw [probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      probeWithRun_typeNames, probeWithRun_signatures, probeWithRun_labels,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, needRewrite, evaluationDemandRewrite,
      needReturnRewrite, reflectedDemandRewrite, runRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      MeTTaZero.metavariable,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The probe with a run constructor passes the declaration gate.** -/
theorem probeWithRun_validate : probeWithRun.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := probeWithRun)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) probeWithRun_rewrites_checked

/-- The probe with a run constructor, as a presentation. -/
def runPresentation : ValidatedLanguageDef := ⟨probeWithRun, probeWithRun_validate⟩

/-- Its static equivalence is that of the probe. -/
theorem probeWithRun_quoteDropOnly : QuoteDropOnly probeWithRun :=
  ⟨rfl, by decide, by decide, by decide⟩

/-! ## Listed theories and the evaluator that runs one -/

/-- **A listing of the steps of a theory given by its terms**: a number for
each term, different for different terms, and for each term the list of its
reducts.  The terms are compared by identity. -/
structure StepListing (source : GSLT.{0}) where
  /-- The number of a term. -/
  code : source.Term → Nat
  injective : Function.Injective code
  /-- The reducts of a term. -/
  next : source.Term → List source.Term
  branches : ∀ term reduct : source.Term, source.rewrites term reduct ↔ reduct ∈ next term
  discrete : ∀ first second : source.Term, source.equations.r first second → first = second

/-- The answers of the evaluator for one subject: the numerals of the reducts
of the term whose numeral the subject contracts to. -/
noncomputable def stepAnswers {Source : Type} (code : Source → Nat) (next : Source → List Source)
    (bindings : Bindings) (subject : Pattern) (answer : String) : List Bindings :=
  open Classical in
  if known : ∃ term, contract (applyBindings bindings subject) = numeral (code term) then
    (next (Classical.choose known)).map fun reduct => (answer, numeral (code reduct)) :: bindings
  else []

/-- **The evaluator of the premises that runs a listed theory.** -/
noncomputable def stepEvaluator {Source : Type} (code : Source → Nat)
    (next : Source → List Source) : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "PrimeStep" [_, subject, .fvar answer] =>
      stepAnswers code next bindings subject answer
  | _ => []

theorem stepAnswers_eq {Source : Type} {code : Source → Nat} (injective : Function.Injective code)
    (next : Source → List Source) {bindings : Bindings} {subject : Pattern} (answer : String)
    {term : Source} (reads : contract (applyBindings bindings subject) = numeral (code term)) :
    stepAnswers code next bindings subject answer =
      (next term).map fun reduct => (answer, numeral (code reduct)) :: bindings := by
  have known : ∃ other, contract (applyBindings bindings subject) = numeral (code other) :=
    ⟨term, reads⟩
  have chosen : Classical.choose known = term :=
    injective (numeral_injective ((Classical.choose_spec known).symm.trans reads))
  unfold stepAnswers
  rw [dif_pos known, chosen]

/-- **The evaluator of a listing reads its subject up to the static
equivalence**: two subjects with one contraction get the same answers. -/
theorem stepAnswers_congr {Source : Type} (code : Source → Nat) (next : Source → List Source)
    (bindings : Bindings) {subject other : Pattern} (answer : String)
    (same : contract (applyBindings bindings subject) = contract (applyBindings bindings other)) :
    stepAnswers code next bindings subject answer = stepAnswers code next bindings other answer := by
  unfold stepAnswers
  generalize contract (applyBindings bindings subject) = first at same ⊢
  generalize contract (applyBindings bindings other) = second at same ⊢
  subst same
  rfl

/-! ## The image of a term -/

/-- `prime-run space subject`. -/
def runPattern (space subject : Pattern) : Pattern := .apply "prime-run" [space, subject]

theorem contract_runPattern (count : Nat) :
    contract (runPattern (.bvar 0) (numeral count)) = runPattern (.bvar 0) (numeral count) := by
  rw [runPattern, contract_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil, contract_numeral]
  rfl

/-- The run of an atom at one space is a process of the extension. -/
theorem runPattern_wellSorted {subject : Pattern}
    (sorted : OpenPatternWellSorted probeWithRun FreeTypeContext.empty [.base "Space"]
      (.base "Atom") subject) :
    OpenPatternWellSorted probeWithRun FreeTypeContext.empty [.base "Space"] (.base "Process")
      (runPattern (.bvar 0) subject) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := sorted
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .constructor (rule := runConstructor) (by decide)
      (fun bare => by
        have checked := (usesBareCollection?_eq_true_iff _).mpr bare
        revert checked
        decide)
      (.cons trivial rfl (.bvar rfl) (.cons trivial rfl typed .nil))
  · simpa [runPattern, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  · simpa [runPattern, isObjectPattern, isObjectPatternList] using object
  · have here : subject.isWellScopedAt 1 = true := scopeSafe
    show (runPattern (.bvar 0) subject).isWellScopedAt 1 = true
    simp [runPattern, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here]

/-- The run of a numeral, as a term. -/
def runTerm (count : Nat) : Contexts.Term probeWithRun openProcess :=
  ⟨runPattern (.bvar 0) (numeral count),
    runPattern_wellSorted
      (numeral_wellSorted_in (lang := probeWithRun) (by decide) (by decide) [.base "Space"] count)⟩

/-! ## The steps of the extension -/

/-- Under the evaluator of a listed theory the run of a term reduces to the
run of each of its reducts. -/
theorem run_step {Source : Type} {code : Source → Nat} (injective : Function.Injective code)
    (next : Source → List Source) {term reduct : Source} (member : reduct ∈ next term) :
    Step (stepEvaluator code next) probeWithRun (runPattern (.bvar 0) (numeral (code term)))
      (runPattern (.bvar 0) (numeral (code reduct))) := by
  refine ⟨1, .rule (rule := runRewrite)
    (initialBindings := [("subject", numeral (code term)), ("space", .bvar 0)])
    (finalBindings := [("answer", numeral (code reduct)), ("subject", numeral (code term)),
      ("space", .bvar 0)])
    (by rw [probeWithRun_rewrites]; simp) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, runRewrite, runPattern, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ stepAnswers code next _ (.fvar "subject") "answer"
    rw [stepAnswers_eq injective next "answer" (term := term)
      (by simp [applyBindings, contract_numeral])]
    exact List.mem_map.mpr ⟨reduct, member, rfl⟩
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [runRewrite, runPattern, applyBindings]

/-- The contraction of an application whose head is not quotation has that
head. -/
theorem head?_contract {pattern : Pattern} {label : String} (head : head? pattern = some label)
    (other : label ≠ "prime-quote") : head? (contract pattern) = some label := by
  obtain ⟨arguments, rfl⟩ := eq_apply_of_head? head
  rw [contract_apply_of_ne other]
  rfl

theorem probeWithRun_category_ne_space : ∀ rule ∈ probeWithRun.terms, rule.category ≠ "Space" := by
  decide

theorem probeWithRun_no_bareCollection :
    ∀ rule ∈ probeWithRun.terms, usesBareCollection? rule = false := by
  decide

/-- At one space the object patterns of the sort `Space` are that space. -/
theorem eq_bvar_of_hasType_space {pattern : Pattern}
    (typed : HasType probeWithRun FreeTypeContext.empty [.base "Space"] pattern (.base "Space"))
    (object : isObjectPattern pattern = true) : pattern = .bvar 0 := by
  generalize same : TypeExpr.base "Space" = type at typed
  cases typed with
  | @bvar _ index _ found =>
      cases index with
      | zero => rfl
      | succ index => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | constructor member _ _ =>
      exact (probeWithRun_category_ne_space _ member (TypeExpr.base.inj same).symm).elim
  | lambda _ => cases same
  | multiLambda _ => cases same
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases same
  | collectionConstructor member parameters _ =>
      have bare := (usesBareCollection?_eq_true_iff _).mpr ⟨_, _, _, parameters⟩
      rw [probeWithRun_no_bareCollection _ member] at bare
      cases bare

theorem probeWithRun_run_params :
    ∀ rule ∈ probeWithRun.terms, rule.label = "prime-run" →
      rule.params = [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")] := by
  decide

/-- A step out of a term that contracts to a run is a step of running: the
evaluator answered for its subject, and the space is kept. -/
theorem run_step_inv {base : BasePremiseEvaluator} {redex contractum image : Pattern}
    (reads : contract redex = runPattern (.bvar 0) image)
    (typed : HasType probeWithRun FreeTypeContext.empty [.base "Space"] redex (.base "Process"))
    (object : isObjectPattern redex = true) (step : Step base probeWithRun redex contractum) :
    ∃ (bindings : Bindings) (subject : Pattern) (final : Bindings),
      contract (applyBindings bindings subject) = image ∧
        final ∈ base probeWithRun bindings
          (.relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"]) ∧
        subject = .fvar "subject" ∧
        applyBindings bindings (.fvar "space") = .bvar 0 ∧
        contractum = applyBindings final runRewrite.right := by
  obtain ⟨rule, member, _, initial, final, matched, premises, rfl⟩ := exists_rule_of_step step
  have runHead : head? (contract redex) = some "prime-run" := by rw [reads]; rfl
  rw [probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have other := head?_contract (head?_of_matched matched) (by decide)
    rw [runHead] at other
    exact absurd other (by decide)
  · have rebuilt : applyBindings initial runRewrite.left = redex :=
      matchPattern_correct matched (by decide)
    have shape : redex = runPattern (applyBindings initial (.fvar "space"))
        (applyBindings initial (.fvar "subject")) := by
      rw [← rebuilt]
      simp [runRewrite, runPattern, applyBindings]
    change PremisesAt base probeWithRun _ initial
      [.relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"]] final
      at premises
    cases premises with
    | cons first rest =>
        cases rest
        cases first with
        | relationQuery answered =>
            rw [shape, runPattern, contract_apply_of_ne (by decide)] at reads
            simp only [runPattern, List.map_cons, List.map_nil, Pattern.apply.injEq,
              List.cons.injEq, and_true, true_and] at reads
            rw [shape, runPattern] at typed object
            obtain ⟨declared, isDeclared, label, argumentsTyped⟩ := hasType_apply_inv typed
            rw [probeWithRun_run_params declared isDeclared label] at argumentsTyped
            obtain ⟨spaceTyped, _⟩ := argumentsTyped.simple_cons_inv
            simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
            exact ⟨initial, .fvar "subject", _, reads.2, answered, rfl,
              eq_bvar_of_hasType_space spaceTyped object.1,
              applyRuleBindings_eq_applyBindings _ _ (by decide)⟩

/-! ## The hosting map -/

/-- Equal terms have equal runs. -/
theorem runTerm_resp {source : GSLT.{0}} (listing : StepListing source) {first second : source.Term}
    (related : source.equations.r first second) :
    (termSetoid (stepEvaluator listing.code listing.next) probeWithRun openProcess).r
      (runTerm (listing.code first)) (runTerm (listing.code second)) := by
  rw [listing.discrete _ _ related]

/-- **A listed theory, in the extended presentation**: a term is read as the
run of the numeral of its number. -/
noncomputable def runMap {source : GSLT.{0}} (listing : StepListing source) :
    ContextMap source.termsAlone
      (contextTheory (stepEvaluator listing.code listing.next) runPresentation) :=
  ContextMap.ofTerms (source := source)
    (target := contextTheory (stepEvaluator listing.code listing.next) runPresentation) openProcess
    (fun term => runTerm (listing.code term))
    (fun related => runTerm_resp listing related)

/-- **Under the evaluator that runs it, the extended presentation hosts every
listed theory on terms.** -/
theorem runMap_hosting {source : GSLT.{0}} (listing : StepListing source) :
    (runMap listing).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := source)
    (target := contextTheory (stepEvaluator listing.code listing.next) runPresentation) openProcess
    (fun term => runTerm (listing.code term))
    (fun related => runTerm_resp listing related)).mpr
    ⟨?_, ?_, ?_⟩
  · intro first second related
    have same := probeWithRun_quoteDropOnly.contract_eq related
    have unfolded : contract (runPattern (.bvar 0) (numeral (listing.code first))) =
        contract (runPattern (.bvar 0) (numeral (listing.code second))) := same
    rw [contract_runPattern, contract_runPattern] at unfolded
    simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
    rw [listing.injective (numeral_injective unfolded)]
  · intro first next step
    exact ⟨runTerm (listing.code first), runTerm (listing.code next), Relation.EqvGen.refl _,
      run_step listing.injective listing.next ((listing.branches first next).mp step),
      Relation.EqvGen.refl _⟩
  · rintro first next ⟨redex, contractum, before, fired, after⟩
    have reads : contract redex.1 = runPattern (.bvar 0) (numeral (listing.code first)) := by
      have same := probeWithRun_quoteDropOnly.contract_eq before
      have unfolded : contract (runPattern (.bvar 0) (numeral (listing.code first))) =
          contract redex.1 := same
      rw [contract_runPattern] at unfolded
      exact unfolded.symm
    obtain ⟨bindings, subject, final, subjectReads, answered, rfl, spaceReads, target⟩ :=
      run_step_inv reads redex.2.1 redex.2.2.2.1 fired
    have answers : final ∈ stepAnswers listing.code listing.next bindings (.fvar "subject")
        "answer" := answered
    rw [stepAnswers_eq listing.injective listing.next "answer" subjectReads] at answers
    obtain ⟨reduct, member, rfl⟩ := List.mem_map.mp answers
    refine ⟨reduct, (listing.branches first reduct).mpr member, ?_⟩
    have image : contractum = runTerm (listing.code reduct) := by
      apply Subtype.ext
      rw [target]
      have space : applyBindings (("answer", numeral (listing.code reduct)) :: bindings)
          (.fvar "space") = applyBindings bindings (.fvar "space") := by
        simp [applyBindings]
      have answer : applyBindings (("answer", numeral (listing.code reduct)) :: bindings)
          (.fvar "answer") = numeral (listing.code reduct) := by
        simp [applyBindings]
      show applyBindings _ (.apply "prime-run" [.fvar "space", .fvar "answer"]) = _
      rw [applyBindings]
      simp only [List.map_cons, List.map_nil, space, answer, spaceReads]
      rfl
    rw [← image]
    exact Relation.EqvGen.symm _ _ after

/-! ## One evaluator for a numbered family -/

/-- The steps of the union of a family of theories: the steps of its
members. -/
inductive UnionStep (family : Nat → GSLT.{0}) :
    (Σ index, (family index).Term) → (Σ index, (family index).Term) → Prop where
  | member {index : Nat} {term next : (family index).Term} :
      (family index).rewrites term next → UnionStep family ⟨index, term⟩ ⟨index, next⟩

/-- **The union of a numbered family of theories given by their terms**: a
term is a term of one member, tagged with the number of the member; terms are
compared by identity. -/
def unionTheory (family : Nat → GSLT.{0}) : GSLT.{0} where
  Term := Σ index, (family index).Term
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := UnionStep family
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **The union of listed theories is listed**: the number of a term pairs
the number of its member with its number there. -/
def unionListing {family : Nat → GSLT.{0}} (listing : (index : Nat) → StepListing (family index)) :
    StepListing (unionTheory family) where
  code := fun term => Nat.pair term.1 ((listing term.1).code term.2)
  injective := by
    rintro ⟨first, term⟩ ⟨second, other⟩ same
    obtain ⟨rfl, codes⟩ := Nat.pair_eq_pair.mp same
    have terms : term = other := (listing first).injective codes
    exact congrArg (Sigma.mk first) terms
  next := fun term => ((listing term.1).next term.2).map (Sigma.mk term.1)
  branches := by
    rintro ⟨index, term⟩ reduct
    constructor
    · intro step
      cases step with
      | member memberStep =>
          exact List.mem_map.mpr ⟨_, ((listing index).branches _ _).mp memberStep, rfl⟩
    · intro listed
      obtain ⟨next, member, rfl⟩ := List.mem_map.mp listed
      exact .member (((listing index).branches _ _).mpr member)
  discrete := fun _ _ same => same

/-- A member of a family, in the union. -/
def memberMap {family : Nat → GSLT.{0}} (listing : (index : Nat) → StepListing (family index))
    (index : Nat) : ContextMap (family index).termsAlone (unionTheory family).termsAlone :=
  ContextMap.ofTerms (source := family index) (target := (unionTheory family).termsAlone) PUnit.unit
    (fun term => (⟨index, term⟩ : (unionTheory family).Term))
    (fun related => congrArg (Sigma.mk index) ((listing index).discrete _ _ related))

/-- The inclusion of a member in the union is hosting. -/
theorem memberMap_hosting {family : Nat → GSLT.{0}}
    (listing : (index : Nat) → StepListing (family index)) (index : Nat) :
    (memberMap listing index).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := family index)
    (target := (unionTheory family).termsAlone) PUnit.unit
    (fun term => (⟨index, term⟩ : (unionTheory family).Term))
    (fun related => congrArg (Sigma.mk index) ((listing index).discrete _ _ related))).mpr
    ⟨?_, ?_, ?_⟩
  · intro first second same
    have terms : first = second := eq_of_heq (Sigma.mk.inj same).2
    rw [terms]
  · intro first next step
    exact UnionStep.member step
  · intro first next step
    generalize origin : (⟨index, first⟩ : (unionTheory family).Term) = start at step
    cases step with
    | @member other term reduct memberStep =>
        obtain ⟨rfl, terms⟩ := Sigma.mk.inj origin
        obtain rfl := eq_of_heq terms
        exact ⟨reduct, memberStep, rfl⟩

/-- **One evaluator of the premises hosts a whole numbered family of listed
theories on terms**: the number of the member travels in the term, inside
the numeral that the run carries. -/
theorem runPresentation_hosts_family {family : Nat → GSLT.{0}}
    (listing : (index : Nat) → StepListing (family index)) (index : Nat) :
    ∃ map : ContextMap (family index).termsAlone
        (contextTheory (stepEvaluator (unionListing listing).code (unionListing listing).next)
          runPresentation), map.Hosting :=
  ⟨(runMap (unionListing listing)).comp (memberMap listing index),
    (runMap_hosting (unionListing listing)).comp (memberMap_hosting listing index)⟩

/-! ## Examples -/

/-- The successor theory: a number reduces to its successor. -/
def successorTheory : GSLT.{0} where
  Term := Nat
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun term next => next = term + 1
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **Positive**: the successor theory is listed. -/
def successorListing : StepListing successorTheory where
  code := fun (term : Nat) => term
  injective := fun _ _ same => same
  next := fun (term : Nat) => [term + 1]
  branches := fun (_ _ : Nat) => List.mem_singleton.symm
  discrete := fun _ _ same => same

/-- **Under the evaluator that runs the successor theory the extended
presentation has reductions of every length**: the run of a number reaches
the run of each larger number, one step for each unit. -/
theorem run_steps (start count : Nat) :
    (contextTheory (stepEvaluator successorListing.code successorListing.next)
      runPresentation).Steps count (runTerm start) (runTerm (start + count)) := by
  induction count generalizing start with
  | zero => exact .zero _
  | succ count ih =>
      have rest := ih (start + 1)
      rw [Nat.add_right_comm] at rest
      exact .succ ⟨runTerm start, runTerm (start + 1), Relation.EqvGen.refl _,
        run_step (Source := Nat) successorListing.injective successorListing.next
          (term := start) (reduct := start + 1) (List.mem_singleton.mpr rfl),
        Relation.EqvGen.refl _⟩ rest

/-- The theory in which zero reduces to every number. -/
def fanTheory : GSLT.{0} where
  Term := Nat
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun term _ => term = 0
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step _ => step

/-- **Negative**: a theory in which one term has infinitely many reducts has
no listing. -/
theorem fanTheory_not_listing : IsEmpty (StepListing fanTheory) := by
  refine ⟨fun listing => ?_⟩
  let reducts : List Nat := listing.next (0 : Nat)
  have every : ∀ reduct : Nat, reduct ∈ reducts := fun reduct =>
    (listing.branches (0 : Nat) reduct).mp rfl
  have bounded : ∀ reduct ∈ reducts, reduct ≤ reducts.sum := fun reduct member =>
    List.le_sum_of_mem member
  exact absurd (bounded _ (every (reducts.sum + 1))) (by omega)

/-- Under the table of the rule `c ⟶ x`, whose right side is a variable that
its left side does not bind, the constant `c` reduces to every term. -/
theorem evaluator_reduces_to_every (term : LF.Term) :
    Dedukti.tableEvaluator.rewrites (interface := ())
      (⟨{Dedukti.ConfluenceExamples.freeRule}, .con "c"⟩ : Dedukti.Tabled)
      ⟨{Dedukti.ConfluenceExamples.freeRule}, term⟩ := by
  have root : Dedukti.RootStep (Dedukti.Theory.ofTable {Dedukti.ConfluenceExamples.freeRule})
      (Dedukti.inst (fun _ => term) Dedukti.ConfluenceExamples.freeRule.lhs)
      (Dedukti.inst (fun _ => term) Dedukti.ConfluenceExamples.freeRule.rhs) :=
    .rule _ (Finset.mem_singleton_self _)
  exact ⟨rfl, Dedukti.Step.root (by simpa [Dedukti.ConfluenceExamples.freeRule] using root)⟩

/-- **Negative**: the rule-table evaluator is not finitely branching, so it
has no listing.  A table may hold a rule whose right side is not determined
by its left side. -/
theorem evaluatorTerms_not_listing : IsEmpty (StepListing (Dedukti.tableEvaluator.gslt ())) := by
  refine ⟨fun listing => ?_⟩
  let start : Dedukti.Tabled := ⟨{Dedukti.ConfluenceExamples.freeRule}, .con "c"⟩
  have every : ∀ index : Nat,
      (⟨{Dedukti.ConfluenceExamples.freeRule}, .var index⟩ : Dedukti.Tabled) ∈ listing.next start :=
    fun index => (listing.branches start _).mp (evaluator_reduces_to_every (.var index))
  have injective : Function.Injective fun index : Nat =>
      (⟨{Dedukti.ConfluenceExamples.freeRule}, .var index⟩ : Dedukti.Tabled) := by
    intro first second same
    have terms : (LF.Term.var first) = .var second := congrArg Dedukti.Tabled.term same
    exact LF.Term.var.inj terms
  exact Set.infinite_range_of_injective injective
    ((List.finite_toSet (listing.next start)).subset (by
      rintro _ ⟨index, rfl⟩
      exact every index))

/-- The one-term theory whose term reduces to itself. -/
def loopTheory : GSLT.{0} where
  Term := Unit
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := fun _ _ => ⟨(), trivial, rfl⟩
  rewrites_resp_right := fun _ _ => trivial

/-- The loop is listed. -/
def loopListing : StepListing loopTheory where
  code := fun _ => 0
  injective := fun _ _ _ => rfl
  next := fun _ => [()]
  branches := fun _ _ => ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => trivial⟩
  discrete := fun _ _ same => same

/-- **Under the evaluator that runs the loop the extended presentation has no
rank.** -/
theorem run_not_rank :
    IsEmpty (contextTheory (stepEvaluator loopListing.code loopListing.next) runPresentation).Rank :=
  ⟨fun ranked => (runMap loopListing).not_preserves_of_cycle_of_rank ranked
    (interface := PUnit.unit) (term := ()) (.single trivial) (runMap_hosting loopListing).preserves⟩

/-! ## Under the silent evaluator the extension has a rank -/

/-- The evaluator of the premises that answers nothing. -/
def silentEvaluator : BasePremiseEvaluator := fun _ _ _ => []

/-- Under the silent evaluator a step of the extension goes along an edge of
the probe. -/
theorem silent_step_heads {source target : Pattern}
    (step : Step silentEvaluator probeWithRun source target) :
    ∃ edge ∈ probeEdges, head? source = some edge.1 ∧ head? target = some edge.2 := by
  obtain ⟨rule, member, _, initial, final, matched, premises, rfl⟩ := exists_rule_of_step step
  rw [probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨("zero-query", "zero-query-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact ⟨("zero-evaluate", "zero-evaluate-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact ⟨("zero-evaluate", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact ⟨("prime-need", "prime-need-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact ⟨("prime-need-answer", "zero-evaluate-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact ⟨("prime-evaluate-name", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · change PremisesAt silentEvaluator probeWithRun _ initial
      [.relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"]] final
      at premises
    cases premises with
    | cons first _ =>
        cases first with
        | relationQuery answered => cases answered

/-- **Negative**: under the silent evaluator the extended presentation has a
rank, so it hosts no theory with a cyclic reduction. -/
def silentRunRank : (contextTheory silentEvaluator runPresentation).Rank where
  rank := fun term => patternRank term.1
  lowers := fun step => by
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    rw [patternRank_congr (probeWithRun_quoteDropOnly.contract_eq before),
      ← patternRank_congr (probeWithRun_quoteDropOnly.contract_eq after)]
    obtain ⟨edge, member, sourceHead, targetHead⟩ := silent_step_heads fired
    simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [patternRank_of_head? sourceHead (by decide), patternRank_of_head? targetHead (by decide)] <;>
      decide

/-- **The contexts of the extended presentation still have a linear size**:
with all contexts it receives no map from a theory that discards or copies,
under any evaluator. -/
def runLinearSize (base : BasePremiseEvaluator) :
    (contextTheory base runPresentation).LinearSize :=
  QuoteDropOnly.linearSize runPresentation probeWithRun_quoteDropOnly base

#print axioms runLinearSize
#print axioms probeWithRun_validate
#print axioms stepAnswers_congr
#print axioms run_step
#print axioms run_step_inv
#print axioms runMap_hosting
#print axioms unionListing
#print axioms memberMap_hosting
#print axioms runPresentation_hosts_family
#print axioms run_steps
#print axioms fanTheory_not_listing
#print axioms evaluatorTerms_not_listing
#print axioms run_not_rank
#print axioms silentRunRank

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
