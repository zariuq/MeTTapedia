import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedContainment

/-!
# The scoped presentation with headed root steps

In the scoped presentation the steps of a run are those by the rules of
either space at the ambient spaces that answer nothing for a run
(`scoped_run_step_iff`), and not beyond them (`scoped_run_needs_silent`): the
ambient root step has a variable as left side, and a run is an atom.

`headedScoped` is the scoped presentation with the eight root steps headed by
the constructors of atoms (`headedRoots`) in place of the ambient root step.
The root step of a run is kept: inside a run the rules of the run's space fire
on every subject.  The evaluator is the evaluator of a region, unchanged.

The presentation passes the declaration gate (`headedScoped_validate`), its
static equivalence is that of quotation and dropping
(`headedScoped_quoteDropOnly`), and every member respects it
(`headedScoped_respectsStatics`): a family of presented candidates indexed by
the ambient space (`headedScopedMember`).

* **The steps of a run are those by the rules of either space, at every
  ambient space** (`headedScoped_run_step_iff`): `run(space, subject)` steps
  to the runs of the steps of `subject` in the member at the ambient space,
  and to the runs of the steps of `subject` in the ambient presentation at
  `space`.  No hypothesis on the ambient space: no root step matches a run.
* **Every step of `headedContained` is a step of `headedScoped`**
  (`step_headedContained_headedScoped`), and `headedScoped` has a step that
  `headedContained` has not (`headedScoped_alone_steps`).  The transitions of
  a run depend on the ambient space (`headedScoped_run_depends_on_ambient`).
* **A run in a run** (`headedScoped_nested_step_iff`): the inner run sees its
  own space and the ambient space, at every ambient space; the space of the
  run around it is asked for the inner run as a whole only
  (`headedScoped_nested_ambient_seen`, `headedScoped_nested_outer_unseen`).
* **No space and no name has a transition, at every stage and under every
  evaluator** (`headedScoped_space_static`, `headedScoped_name_static`).
* **Nothing is lost for tables without a variable as a left side**
  (`headedScoped_atom_step_iff`, `headedScoped_hostOf_tabularAt`,
  `headedScoped_hostOf_scopedTabularAt`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory inst substitute inst_eq_substitute patternVars usesOnly
    withChoice chooseLeft chooseRight normal_of_normalTest)
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

variable {admits : Pattern → Bool}

/-! ## The scoped presentation needs an ambient space that answers nothing for a run -/

/-- The space that stores an equation between two runs answers nothing for
the atom of a term. -/
theorem runEquationSpace_quiet_on_atoms {depth : Nat} {term : LF.Term} {answer : Pattern} :
    answer ∉ matchResults (contract runEquationSpace.1) (atomAt depth term) := by
  intro found
  have spaceFixed : contract runEquationSpace.1 = spaceOfAtoms [runEquation] := by decide
  rw [spaceFixed, mem_matchResults_spaceOfAtoms] at found
  obtain ⟨atom, member, inAtom⟩ := found
  obtain rfl := List.mem_singleton.mp member
  have leftRead : asRule (runPattern emptySpace (atomAt 0 (.srt .type))) =
      runPattern emptySpace (atomAt 0 (.srt .type)) := by decide
  have rightRead : asRule (runPattern emptySpace (atomAt 0 (.srt .kind))) =
      runPattern emptySpace (atomAt 0 (.srt .kind)) := by decide
  rw [runEquation, atomResults_equation _ (by rw [leftRead]; decide) (by rw [rightRead]; decide),
    leftRead] at inAtom
  obtain ⟨bindings, matched, -⟩ := List.mem_map.mp inAtom
  exact atomAt_not_matched (label := "prime-run") (by decide) matched

/-- **Negative: at an ambient space that answers for a run, a step of a run
of the scoped presentation need not be the run of a step of its subject.**
At the space that stores an equation between two runs, the run in the empty
space of the application of the sort of types to itself has a step in its
function; that application has that step neither in the scoped member at the
ambient space nor in the ambient presentation at the space of the run. -/
theorem scoped_run_needs_silent :
    Step (regionEvaluator anySubject runEquationSpace.1) scopedRun
        (runPattern emptySpace (atomAt 0 (.app (.srt .type) (.srt .type))))
        (runPattern emptySpace (.apply "App" [atomAt 0 (.srt .kind), atomAt 0 (.srt .type)])) ∧
      ¬ (Step (regionEvaluator anySubject runEquationSpace.1) scopedRun
            (atomAt 0 (.app (.srt .type) (.srt .type)))
            (.apply "App" [atomAt 0 (.srt .kind), atomAt 0 (.srt .type)]) ∨
          Step (regionEvaluator anySubject emptySpace) ambient
            (atomAt 0 (.app (.srt .type) (.srt .type)))
            (.apply "App" [atomAt 0 (.srt .kind), atomAt 0 (.srt .type)])) := by
  refine ⟨step_contained_scoped anySubject_ambient_reaches_inside.1, ?_⟩
  rintro (viaAmbient | ⟨fuel, viaRun⟩)
  · obtain ⟨fuel, bounded⟩ := step_any_iff_ambientEvaluator.mp
      ((runFree_step_iff_scoped (tokens_run_atomAt _ 0)).mp viaAmbient)
    obtain ⟨next, -, sourceStep⟩ := ambient_stepAt_sound_of (theory := Theory.empty)
      (fun found => absurd found runEquationSpace_quiet_on_atoms) fuel bounded
    exact normal_of_normalTest pureCover _ (by decide) _ sourceStep
  · exact anySubject_ambient_reaches_inside.2 _ ⟨fuel, stepAt_ambient_contained viaRun⟩

/-! ## The presentation -/

/-- **The scoped presentation with headed root steps**: the scoped
presentation, with the eight root steps in place of the ambient root step. -/
def headedScoped : LanguageDef :=
  { name := "metta-prime-ambient-space-scoped-run-headed-roots"
    types := [MeTTaZero.atomType, MeTTaZero.spaceType, nameType]
    terms :=
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor]
    equations := [quoteDropEquation]
    rewrites := (fixedRules ++ [releaseRule]) ++ headedRoots ++
      (sharedRunRules ++ [runSubjectRule]) }

theorem headedScoped_rewrites : headedScoped.rewrites =
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
      runLamDomainRule, runLamBodyRule, runSubjectRule] :=
  rfl

/-- The rewrites of the presentation, in three groups: those of an atom that
ask nothing, the eight root steps, and those about a run. -/
theorem mem_headedScoped_rewrites {rule : RewriteRule} :
    rule ∈ headedScoped.rewrites ↔
      rule ∈ [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
        lamBodyRule, releaseRule] ∨ rule ∈ headedRoots ∨
        rule ∈ [runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule,
          runPiBodyRule, runLamDomainRule, runLamBodyRule, runSubjectRule] := by
  show rule ∈ (fixedRules ++ [releaseRule]) ++ headedRoots ++
      (sharedRunRules ++ [runSubjectRule]) ↔ _
  rw [List.mem_append, List.mem_append]
  exact or_assoc

theorem headedScoped_typeNames :
    headedScoped.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

theorem headedScoped_signatures :
    RewriteValidationCertificate.constructorSignatures headedScoped =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2)] := by
  decide

theorem headedScoped_labels :
    RewriteValidationCertificate.constructorLabels headedScoped =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi"] := by
  decide

/-- Every rewrite of the presentation passes its row of the declaration
gate. -/
theorem headedScoped_rewrites_checked :
    ∀ rewrite ∈ headedScoped.rewrites,
      RewriteValidationCertificate.check headedScoped rewrite = true := by
  intro rewrite member
  rw [headedScoped_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      headedScoped_typeNames, headedScoped_signatures, headedScoped_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, headedRootRule,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runSubjectRule, runPattern,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The presentation passes the declaration gate.** -/
theorem headedScoped_validate : headedScoped.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks (lang := headedScoped)
    (RewriteValidationCertificate.validate_signature_of_same_data (left := containedRun) rfl rfl rfl contained_signature_valid) (by decide +kernel) headedScoped_rewrites_checked

/-- The presentation, as a presentation. -/
def headedScopedPresentation : ValidatedLanguageDef := ⟨headedScoped, headedScoped_validate⟩

/-- **It differs from the scoped presentation by its root steps alone**: the
same constructors, the same equation, and the sixteen rewrites of the scoped
presentation other than the ambient root step. -/
theorem headedScoped_differs :
    headedScoped.terms = scopedRun.terms ∧
      headedScoped.equations = scopedRun.equations ∧
        (∀ rule ∈ scopedRun.rewrites, rule ≠ rootRule → rule ∈ headedScoped.rewrites) ∧
          rootRule.name ∉ headedScoped.rewrites.map (·.name) := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  intro rule member other
  rw [scoped_rewrites] at member
  rw [headedScoped_rewrites]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

/-! ## Its static equivalence, and its evaluator -/

/-- **The static equivalence is that of quotation and dropping.** -/
theorem headedScoped_quoteDropOnly : QuoteDropOnly headedScoped :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem headedScoped_quoteDropSorted : QuoteDropSorted headedScoped :=
  ⟨by decide, by decide⟩

theorem headedScoped_carriesAtoms : CarriesAtoms headedScoped := by
  unfold CarriesAtoms
  decide

theorem headedScoped_declaresRun : DeclaresRun headedScoped := by
  unfold DeclaresRun
  decide

theorem headedScoped_namesOnlyDropped : NamesOnlyDropped headedScoped unquotedSorts :=
  atomsReduce_namesOnlyDropped

/-- The premises that the presentation hands to its evaluator. -/
theorem headedScoped_premises : ∀ premise ∈ presentedPremises headedScoped,
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
        .congruence (.fvar "X") (.fvar "Y")] :=
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
theorem headedScoped_respectsStatics (admits : Pattern → Bool) (ambientSpace : Pattern) :
    RespectsStatics (regionEvaluator admits ambientSpace) headedScoped :=
  regionEvaluator_respectsStatics_of_queries headedScoped_quoteDropOnly
    headedScoped_premises admits ambientSpace

/-- A space of the presentation. -/
abbrev HeadedScopedSpace : Type := Contexts.Term headedScoped closedSpace

/-- **The member of the family at an ambient space**, as a presented
candidate: the presentation under the evaluator of a region. -/
def headedScopedMember (admits : Pattern → Bool) (space : HeadedScopedSpace) :
    PresentedCandidate where
  presentation := headedScopedPresentation
  evaluator := regionEvaluator admits space.1
  respects := headedScoped_respectsStatics admits space.1

/-- The theory of the presentation at an ambient space, with all its
contexts. -/
abbrev headedScopedTheory (admits : Pattern → Bool) (space : Pattern) : ContextTheory.{0} :=
  contextTheory (regionEvaluator admits space) headedScopedPresentation

/-! ## Only an atom has a transition, at every stage -/

/-- **Every rewrite of the presentation is headed by a constructor of
atoms.** -/
theorem headedScoped_headedIn_atom : rewritesHeadedIn headedScoped ["Atom"] = true := by decide

/-- **Negative**: the scoped presentation has a rewrite with no head. -/
theorem scoped_not_headedIn_atom : rewritesHeadedIn scopedRun ["Atom"] = false := by decide

/-- **No space has a transition**, at every stage and under every
evaluator. -/
theorem headedScoped_space_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term headedScoped ⟨.base "Space", stage⟩) :
    ¬ TermStep base headedScoped term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts headedScoped_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-- **No name has a transition**, at every stage and under every
evaluator. -/
theorem headedScoped_name_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term headedScoped ⟨.base "CandidateName", stage⟩) :
    ¬ TermStep base headedScoped term next := by
  intro step
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts headedScoped_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact absurd (TypeExpr.base.inj type) (by decide)

/-! ## The presentation with headed root steps and a contained run, inside this one -/

/-- **Every step of `headedContained` is a step of `headedScoped`**, under
one evaluator.  Beta, release and the step of a run, each beneath a run, are
found through the congruence of the subject of a run. -/
theorem stepAt_headedContained_headedScoped {ambientSpace : Pattern} :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) headedContained fuel source target →
        Step (regionEvaluator admits ambientSpace) headedScoped source target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedContained_rewrites.mp member with plain | root | run
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
          rw [applied]
          exact ⟨1, step_beta (by simp [headedScoped_rewrites]) domain body argument binder⟩
        · obtain ⟨function, argument, moved, rfl, inner, applied⟩ :=
            appFunction_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_appFunction (by simp [headedScoped_rewrites]) argument lifted⟩
        · obtain ⟨function, argument, moved, rfl, inner, applied⟩ :=
            appArgument_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_appArgument (by simp [headedScoped_rewrites]) function lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ :=
            piDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_piDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_piBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ :=
            lamDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_lamDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
        · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_lamBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
        · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
          rw [applied]
          exact ⟨1, step_release (by simp [headedScoped_rewrites]) atom⟩
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        rw [applied]
        exact ⟨1, step_headedRoot (mem_headedScoped_rewrites.mpr (.inr (.inl root))) matched
          (matchPattern_correct matched exact) found⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨space, subject, answer, rfl, found, applied⟩ :=
            regionRunRoot_inv matched premises
          rw [applied]
          exact ⟨1, step_regionRunRoot (by simp [headedScoped_rewrites]) found⟩
        · obtain ⟨space, function, argument, moved, rfl, inner, applied⟩ :=
            runAppFunction_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppFunction (by simp [headedScoped_rewrites]) argument
            lifted⟩
        · obtain ⟨space, function, argument, moved, rfl, inner, applied⟩ :=
            runAppArgument_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppArgument (by simp [headedScoped_rewrites]) function
            lifted⟩
        · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
            runPiDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiDomain (by simp [headedScoped_rewrites]) body binder
            lifted⟩
        · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
            runPiBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiBody (by simp [headedScoped_rewrites]) domain binder
            lifted⟩
        · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
            runLamDomain_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamDomain (by simp [headedScoped_rewrites]) body binder
            lifted⟩
        · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
            runLamBody_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamBody (by simp [headedScoped_rewrites]) domain binder
            lifted⟩
        · obtain ⟨space, domain, binder, body, argument, rfl, applied⟩ :=
            runBeta_inv matched premises
          rw [applied]
          exact ⟨2, step_runSubject (by simp [headedScoped_rewrites]) space
            (step_beta (by simp [headedScoped_rewrites]) domain body argument binder)⟩
        · obtain ⟨space, atom, rfl, applied⟩ := runRelease_inv matched premises
          rw [applied]
          exact ⟨2, step_runSubject (by simp [headedScoped_rewrites]) space
            (step_release (by simp [headedScoped_rewrites]) atom)⟩
        · obtain ⟨outer, space, subject, next, rfl, inner, applied⟩ :=
            runBeneathRun_inv matched premises
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runSubject (by simp [headedScoped_rewrites]) outer lifted⟩

/-- The same for steps. -/
theorem step_headedContained_headedScoped {ambientSpace : Pattern} {source target : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) headedContained source target) :
    Step (regionEvaluator admits ambientSpace) headedScoped source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact stepAt_headedContained_headedScoped fuel bounded

/-! ## The steps of a run are those by the rules of either space -/

/-- **A step of a run is the run of a step of its subject**, at every ambient
space: a step of the member at the ambient space, or a step of the ambient
presentation at the space of the run. -/
theorem headedScoped_run_stepAt_inv (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) headedScoped fuel (runPattern space subject)
          target →
        ∃ next, target = runPattern space next ∧
          (Step (regionEvaluator admits ambientSpace) headedScoped subject next ∨
            Step (regionEvaluator admits space) ambient subject next) := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedScoped_rewrites.mp member with plain | root | run
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
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨otherSpace, inner, answer, shape, found, applied⟩ :=
            regionRunRoot_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨answer, applied, .inr ⟨1, step_ambientRoot (by simp [ambient_rewrites]) found⟩⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppFunction_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_appFunction (by simp [headedScoped_rewrites]) argument lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_appFunction (by simp [ambient_rewrites]) argument lifted⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppArgument_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_appArgument (by simp [headedScoped_rewrites]) function lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_appArgument (by simp [ambient_rewrites]) function lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_piDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_piDomain (by simp [ambient_rewrites]) body binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_piBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_piBody (by simp [ambient_rewrites]) domain binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_lamDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_lamDomain (by simp [ambient_rewrites]) body binder lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          obtain ⟨reached, same, either⟩ := ih inner
          obtain ⟨-, rfl⟩ := runPattern_injective same
          refine ⟨_, applied, either.imp ?_ ?_⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_lamBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
          · rintro ⟨count, lifted⟩
            exact ⟨count + 1, step_lamBody (by simp [ambient_rewrites]) domain binder lifted⟩
        · obtain ⟨otherSpace, inner, moved, shape, innerStep, applied⟩ :=
            runSubject_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          exact ⟨moved, applied, .inl ⟨fuel, innerStep⟩⟩

/-- **A step of the ambient presentation at the space of a run is a step of
the run**, at every ambient space: a rule at the root is found by the root
step of the run, a position beneath the root by a congruence beneath the run,
and beta and release by the congruence of its subject. -/
theorem headedScoped_run_of_ambient_stepAt {space : Pattern} (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {subject next : Pattern},
      StepAt (regionEvaluator admits space) ambient fuel subject next →
        Step (regionEvaluator admits ambientSpace) headedScoped (runPattern space subject)
          (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro subject next step; cases step
  | succ fuel ih =>
      intro subject next step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [headedScoped_rewrites]) space
          (step_beta (by simp [headedScoped_rewrites]) domain body argument binder)⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppFunction (by simp [headedScoped_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppArgument (by simp [headedScoped_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamDomain (by simp [headedScoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamBody (by simp [headedScoped_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [headedScoped_rewrites]) space
          (step_release (by simp [headedScoped_rewrites]) atom)⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_regionRunRoot (by simp [headedScoped_rewrites]) found⟩

/-- **A step of the subject of a run, in the member at the ambient space, is a
step of the run**: the ambient space reaches in. -/
theorem headedScoped_run_of_step {ambientSpace : Pattern} (space : Pattern)
    {subject next : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) headedScoped subject next) :
    Step (regionEvaluator admits ambientSpace) headedScoped (runPattern space subject)
      (runPattern space next) := by
  obtain ⟨fuel, bounded⟩ := step
  exact ⟨fuel + 1, step_runSubject (by simp [headedScoped_rewrites]) space bounded⟩

/-- **The steps of a run are those by the rules of either space, at every
ambient space.**  `run(space, subject)` steps to the runs of the steps of
`subject` in the member at the ambient space, and to the runs of the steps of
`subject` in the ambient presentation at `space`. -/
theorem headedScoped_run_step_iff {ambientSpace space subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) headedScoped (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        (Step (regionEvaluator admits ambientSpace) headedScoped subject next ∨
          Step (regionEvaluator admits space) ambient subject next) := by
  constructor
  · rintro ⟨fuel, step⟩
    exact headedScoped_run_stepAt_inv ambientSpace fuel step
  · rintro ⟨next, rfl, viaAmbient | ⟨fuel, viaRun⟩⟩
    · exact headedScoped_run_of_step space viaAmbient
    · exact headedScoped_run_of_ambient_stepAt ambientSpace fuel viaRun

/-- **A run in a run**: where the outer space answers nothing for a run, the
steps of `run(outer, run(inner, subject))` are the runs of the runs of the
steps of `subject` in the member at the ambient space, and in the ambient
presentation at the inner space.  No hypothesis on the ambient space. -/
theorem headedScoped_nested_step_iff {ambientSpace outer inner subject target : Pattern}
    (outerSilent : RunSilent admits outer) :
    Step (regionEvaluator admits ambientSpace) headedScoped
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        (Step (regionEvaluator admits ambientSpace) headedScoped subject next ∨
          Step (regionEvaluator admits inner) ambient subject next) := by
  rw [headedScoped_run_step_iff]
  constructor
  · rintro ⟨middle, rfl, viaAmbient | viaOuter⟩
    · obtain ⟨next, rfl, either⟩ := headedScoped_run_step_iff.mp viaAmbient
      exact ⟨next, rfl, either⟩
    · exact absurd viaOuter (ambient_run_normal outerSilent inner subject middle)
  · rintro ⟨next, rfl, either⟩
    exact ⟨runPattern inner next, rfl, .inl (headedScoped_run_step_iff.mpr ⟨next, rfl, either⟩)⟩

/-! ## Atoms outside a run: tables without a variable as a left side -/

/-- A step from the atom of a term is the atom of a step of the term, in
every theory whose steps at the root include what the ambient space answers
for the atoms of terms. -/
theorem headedScoped_atom_stepAt_sound {ambientSpace : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ admittedAnswers admits ambientSpace (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) headedScoped fuel (atomAt depth source)
          target →
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedScoped_rewrites.mp member with plain | root | run
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, shape, applied⟩ := beta_inv matched premises
          obtain ⟨function, argumentTerm, rfl, functionEq, rfl⟩ := atomAt_eq_app shape
          obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam functionEq.symm
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          exact ⟨subst0 argumentTerm bodyTerm, by rw [applied, instantiateBVar_atomAt],
            Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appFunction_inv matched premises
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.app nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.appFunction .hole second)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appArgument_inv matched premises
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.app first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.appArgument first .hole)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piDomain_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.pi nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.piDomain .hole second)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piBody_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.pi first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.piBody first .hole)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ :=
            lamDomain_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.lam nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.lamDomain .hole second)⟩
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := lamBody_inv matched premises
          obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.lam first nextTerm, by rw [applied]; rfl,
            innerStep.plug (.lamBody first .hole)⟩
        · exact absurd matched (atomAt_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers found
        exact ⟨nextTerm, applied, rootStep⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))

/-- Every step of a term, by the rules of a list none of whose left sides is
a variable, is a step between the atoms. -/
theorem headedScoped_atom_stepAt_complete (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (regionEvaluator admits (ruleSpace rules)) headedScoped fuel
      (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              have fired := step_beta (base := regionEvaluator admits (ruleSpace rules))
                (lang := headedScoped) (by simp [headedScoped_rewrites])
                (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
              rw [instantiateBVar_atomAt] at fired
              exact ⟨1, fired⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_headedRoot_atomAt
                (fun other inRoots => mem_headedScoped_rewrites.mpr (.inr (.inl inRoots)))
                (atomAt_inst_ne_bvar (firstOrder rule (listed rule member)).1
                  (headed rule (listed rule member)) assignment depth) ?_⟩
              refine mem_admittedAnswers.mpr ⟨?_, ?_⟩
              · rw [contract_atomAt]
                exact admitsAtoms _ _
              · rw [contract_ruleSpace, contract_atomAt]
                exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [headedScoped_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [headedScoped_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [headedScoped_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [headedScoped_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [headedScoped_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [headedScoped_rewrites])
            (atomAt depth domain) none inner⟩

/-- **Outside a run the presentation computes, on the atom of a term, by beta
and by the rules that the ambient space stores**, for a list of rules none of
whose left sides is a variable. -/
theorem headedScoped_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) headedScoped (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    refine headedScoped_atom_stepAt_sound (fun found => ?_) fuel step
    have inSpace := (mem_admittedAnswers.mp found).2
    rw [contract_ruleSpace, contract_atomAt] at inSpace
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound inSpace
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment ((rulesIff rule).mpr inRules))⟩
  · rintro ⟨next, rfl, step⟩
    exact headedScoped_atom_stepAt_complete admitsAtoms firstOrder bound headed
      (fun rule member => (rulesIff rule).mp member) undefined step depth

variable {declared : Contexts.Interface → Prop}

/-- **On terms: at the space of a table of first-order rules with bound right
sides none of whose left sides is a variable, the presentation is a host of
the theories given by that table.** -/
theorem headedScoped_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (headedScopedTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨termsMapIn theory _ headedScoped_carriesAtoms,
    termsMapIn_hosting headedScoped_carriesAtoms headedScoped_quoteDropOnly
      headedScoped_quoteDropSorted headedScoped_namesOnlyDropped
      (headedScoped_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With contexts: a reading of the presentation, at the space of such a
table, in which the holes of atoms are free is a host, with all contexts, of
the theories given by the table** on the terms with free variables below a
width, for every width. -/
theorem headedScoped_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits)
    {table : RuleTable} (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index)
    (free : AtomsFree declared) :
    HostOf ((headedScopedTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMapIn theory _ headedScoped_carriesAtoms free width,
    scopedMapIn_hosting headedScoped_carriesAtoms headedScoped_quoteDropOnly
      headedScoped_quoteDropSorted headedScoped_namesOnlyDropped
      (headedScoped_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

/-! ## Instances -/

/-- The atom of `choose heads tails` has no step at the empty ambient space,
without a guard. -/
theorem headedScoped_coin_normal_at_empty (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [])) headedScoped (atomAt 0 coin) target := by
  intro step
  obtain ⟨reduct, -, sourceStep⟩ := (headedScoped_atom_step_iff anySubject_admitsAtoms
    (rules := []) noRules_admitted.1 noRules_admitted.2
    (fun _ member => absurd member List.not_mem_nil) (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- The atom of `choose heads tails` has no step in the ambient presentation
at the empty space, without a guard. -/
theorem ambient_coin_normal_at_empty (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [])) ambient (atomAt 0 coin) target := by
  intro step
  obtain ⟨reduct, -, sourceStep⟩ := (guarded_atom_step_iff anySubject_admitsAtoms
    (rules := []) noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **Positive: the ambient space reaches into a run.**  The run of
`choose heads tails` in the empty space steps to the run of `heads`, at the
ambient space of the two rules of choice and without a guard. -/
theorem headedScoped_runCoin_steps :
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) headedScoped
      (runPattern (ruleSpace []) (atomAt 0 coin))
      (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) :=
  headedScoped_run_step_iff.mpr ⟨_, rfl, .inl ((headedScoped_atom_step_iff anySubject_admitsAtoms
    choiceRules_admitted.1 choiceRules_admitted.2 choiceRules_headed withChoice_rules
    (fun _ => rfl)).mpr ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩)⟩

/-- **Negative**: at the empty ambient space that run has no step. -/
theorem headedScoped_runCoin_normal_at_empty (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [])) headedScoped
      (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  intro step
  obtain ⟨next, -, viaAmbient | viaRun⟩ := headedScoped_run_step_iff.mp step
  · exact headedScoped_coin_normal_at_empty next viaAmbient
  · exact ambient_coin_normal_at_empty next viaRun

/-- **The transitions of a run depend on the ambient space**: the run of
`choose heads tails` in the empty space has a step at the ambient space of
the two rules of choice, and no step at the empty ambient space. -/
theorem headedScoped_run_depends_on_ambient :
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) headedScoped
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject (ruleSpace [])) headedScoped
          (runPattern (ruleSpace []) (atomAt 0 coin)) target :=
  ⟨headedScoped_runCoin_steps, headedScoped_runCoin_normal_at_empty⟩

/-- **A step that only this presentation has.**  At the ambient space of the
two rules of choice the run of `choose heads tails` in the empty space has a
step here and none in `headedContained`. -/
theorem headedScoped_alone_steps :
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) headedScoped
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) headedContained
          (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  refine ⟨headedScoped_runCoin_steps, fun target step => ?_⟩
  obtain ⟨next, -, sourceStep⟩ := (headed_runAtom_step_iff anySubject_admitsAtoms
    (ruleSpace [chooseLeft, chooseRight]) (rules := []) noRules_admitted.1 noRules_admitted.2
    (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **Positive, a run in a run**: the inner run sees the ambient space.  The
run of `choose heads tails` in the empty space, inside a run in the empty
space, steps at the ambient space of the two rules of choice. -/
theorem headedScoped_nested_ambient_seen :
    Step (regionEvaluator anySubject (ruleSpace [chooseLeft, chooseRight])) headedScoped
      (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 coin)))
      (runPattern (ruleSpace []) (runPattern (ruleSpace []) (atomAt 0 (.con "heads")))) :=
  headedScoped_run_step_iff.mpr ⟨_, rfl, .inl headedScoped_runCoin_steps⟩

/-- **Negative, a run in a run**: the inner run does not see the space of the
run around it.  The run of `choose heads tails` in the empty space, inside a
run in the space of the two rules of choice, has no step at the empty ambient
space. -/
theorem headedScoped_nested_outer_unseen (target : Pattern) :
    ¬ Step (regionEvaluator anySubject (ruleSpace [])) headedScoped
      (runPattern (ruleSpace [chooseLeft, chooseRight])
        (runPattern (ruleSpace []) (atomAt 0 coin))) target := by
  intro step
  obtain ⟨next, -, viaAmbient | viaRun⟩ := (headedScoped_nested_step_iff
    (choiceSpace_runSilent anySubject)).mp step
  · exact headedScoped_coin_normal_at_empty next viaAmbient
  · exact ambient_coin_normal_at_empty next viaRun

/-- **A weak evaluator, scoping and static spaces together, under the
unchanged evaluator.**  Without a guard the evaluator answers the queries of
the eight root steps and the premise of the root step of a run by one
function that answers by stored rules; at every ambient space the steps of a
run are those by the rules of either space; and no space and no name has a
transition, at every stage and under every evaluator. -/
theorem headedScoped_weak_scoped_static :
    (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "AmbientStep" [subject, .fvar "answer"]) =
          (admittedAnswers anySubject ambientSpace (applyBindings bindings subject)).map
            fun result => ("answer", result) :: bindings) ∧
      (∀ ambientSpace : Pattern, AuthoredEvaluators.AnswersRunBy
        (regionEvaluator anySubject ambientSpace) (admittedAnswers anySubject)) ∧
      AuthoredEvaluators.AnswersByStoredRules (admittedAnswers anySubject) ∧
      (∀ ambientSpace space subject target : Pattern,
        Step (regionEvaluator anySubject ambientSpace) headedScoped (runPattern space subject)
            target ↔
          ∃ next, target = runPattern space next ∧
            (Step (regionEvaluator anySubject ambientSpace) headedScoped subject next ∨
              Step (regionEvaluator anySubject space) ambient subject next)) ∧
      (∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
          (term next : Contexts.Term headedScoped ⟨.base "Space", stage⟩),
        ¬ TermStep base headedScoped term next) ∧
      ∀ (base : BasePremiseEvaluator) (stage : List TypeExpr)
        (term next : Contexts.Term headedScoped ⟨.base "CandidateName", stage⟩),
        ¬ TermStep base headedScoped term next :=
  ⟨regionEvaluator_ambientQuery anySubject, regionEvaluator_answersRunBy anySubject,
    admittedAnswers_any_answersByStoredRules, fun _ _ _ _ => headedScoped_run_step_iff,
    fun _ _ term next => headedScoped_space_static term next,
    fun _ _ term next => headedScoped_name_static term next⟩

#print axioms runEquationSpace_quiet_on_atoms
#print axioms scoped_run_needs_silent
#print axioms headedScoped_rewrites
#print axioms mem_headedScoped_rewrites
#print axioms headedScoped_typeNames
#print axioms headedScoped_signatures
#print axioms headedScoped_labels
#print axioms headedScoped_rewrites_checked
#print axioms headedScoped_validate
#print axioms headedScoped_differs
#print axioms headedScoped_quoteDropOnly
#print axioms headedScoped_quoteDropSorted
#print axioms headedScoped_carriesAtoms
#print axioms headedScoped_declaresRun
#print axioms headedScoped_namesOnlyDropped
#print axioms headedScoped_premises
#print axioms headedScoped_respectsStatics
#print axioms headedScopedMember
#print axioms headedScoped_headedIn_atom
#print axioms scoped_not_headedIn_atom
#print axioms headedScoped_space_static
#print axioms headedScoped_name_static
#print axioms stepAt_headedContained_headedScoped
#print axioms step_headedContained_headedScoped
#print axioms headedScoped_run_stepAt_inv
#print axioms headedScoped_run_of_ambient_stepAt
#print axioms headedScoped_run_of_step
#print axioms headedScoped_run_step_iff
#print axioms headedScoped_nested_step_iff
#print axioms headedScoped_atom_stepAt_sound
#print axioms headedScoped_atom_stepAt_complete
#print axioms headedScoped_atom_step_iff
#print axioms headedScoped_hostOf_tabularAt
#print axioms headedScoped_hostOf_scopedTabularAt
#print axioms headedScoped_coin_normal_at_empty
#print axioms ambient_coin_normal_at_empty
#print axioms headedScoped_runCoin_steps
#print axioms headedScoped_runCoin_normal_at_empty
#print axioms headedScoped_run_depends_on_ambient
#print axioms headedScoped_alone_steps
#print axioms headedScoped_nested_ambient_seen
#print axioms headedScoped_nested_outer_unseen
#print axioms headedScoped_weak_scoped_static

end Mettapedia.Logic.HostingStyles.AmbientRegions
