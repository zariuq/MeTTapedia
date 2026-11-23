import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.PrimeCandidate.PresentedSteps

/-!
# A space as a term

In the probe the sort `Space` has no constructor, so no closed term is a
request and no reduction between closed terms has two steps.  This module
extends the probe with the run constructor by three constructors,

    prime-space-empty : Space
    prime-space-add   : Atom × Space → Space
    prime-variable    : Atom → Atom

the empty space, the addition of an atom to a space, and a variable atom, and
adds no rewrite and no equation (`probeWithSpace`, validated:
`spacePresentation`).

* A space is now a term: the list of its atoms, in the order of their
  addition (`spaceOfAtoms`, `storedAtoms_spaceOfAtoms`,
  `spaceOfAtoms_wellSorted`).  Two spaces with the same atoms in another
  order are two terms, and they are apart (`spaceOfAtoms_apart`): the static
  equivalence is still that of quotation and dropping alone
  (`probeWithSpace_quoteDropOnly`).
* **Closed requests exist** (`closedEvaluationTerm`), and a reduction between
  closed terms has three steps under an evaluator that answers every Need
  (`space_closed_steps_three`), where the probe has none of two steps.
* **The rank of the probe survives outside running**: for every evaluator a
  transition lowers it or goes from a run to a run
  (`space_termStep_lowers_or_runs`); under the evaluator that answers nothing
  it is a rank (`silentSpaceRank`).  What an evaluator that answers the run
  premise does to it is the subject of `MatchingEvaluator`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## The extension -/

/-- The empty space. -/
def emptySpaceConstructor : GrammarRule := plainConstructor "prime-space-empty" "Space" []

/-- The addition of an atom to a space. -/
def addAtomConstructor : GrammarRule :=
  plainConstructor "prime-space-add" "Space"
    [.simple "atom" (.base "Atom"), .simple "rest" (.base "Space")]

/-- A variable atom, named by an atom. -/
def variableConstructor : GrammarRule :=
  plainConstructor "prime-variable" "Atom" [.simple "index" (.base "Atom")]

/-- **The probe with the run constructor and a space that is a term.** -/
def probeWithSpace : LanguageDef :=
  { probeWithRun with
    name := "metta-prime-spec-probe-with-space"
    terms := probeWithRun.terms ++
      [emptySpaceConstructor, addAtomConstructor, variableConstructor] }

/-- It has the rewrites of the probe with the run constructor. -/
theorem probeWithSpace_rewrites : probeWithSpace.rewrites = probeWithRun.rewrites := rfl

theorem probeWithSpace_typeNames : probeWithSpace.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"] := by
  decide

theorem probeWithSpace_signatures :
    RewriteValidationCertificate.constructorSignatures probeWithSpace =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("prime-run", 2),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1)] := by
  decide

theorem probeWithSpace_labels :
    RewriteValidationCertificate.constructorLabels probeWithSpace =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "prime-run", "prime-space-empty", "prime-space-add",
        "prime-variable"] := by
  decide

/-- Every rewrite of the extension passes its row of the declaration gate. -/
theorem probeWithSpace_rewrites_checked :
    ∀ rewrite ∈ probeWithSpace.rewrites,
      RewriteValidationCertificate.check probeWithSpace rewrite = true := by
  intro rewrite member
  rw [probeWithSpace_rewrites, probeWithRun_rewrites] at member
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
      probeWithSpace_typeNames, probeWithSpace_signatures, probeWithSpace_labels,
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

/-- **The extension passes the declaration gate.** -/
theorem probeWithSpace_validate : probeWithSpace.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := probeWithSpace)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) probeWithSpace_rewrites_checked

/-- The extension, as a presentation. -/
def spacePresentation : ValidatedLanguageDef := ⟨probeWithSpace, probeWithSpace_validate⟩

/-- **Its static equivalence is that of the probe**: the three constructors
come with no equation, and a space is no bag. -/
theorem probeWithSpace_quoteDropOnly : QuoteDropOnly probeWithSpace :=
  ⟨rfl, by decide, by decide, by decide⟩

theorem probeWithSpace_quoteDropSorted : QuoteDropSorted probeWithSpace := ⟨by decide, by decide⟩

/-- **Negative**: the probe with the run constructor declares none of the
three. -/
theorem probeWithRun_no_space_constructor :
    emptySpaceConstructor ∉ probeWithRun.terms ∧ addAtomConstructor ∉ probeWithRun.terms ∧
      variableConstructor ∉ probeWithRun.terms := by
  decide

/-! ## Spaces and variable atoms, as patterns -/

/-- The empty space. -/
def emptySpace : Pattern := .apply "prime-space-empty" []

/-- A space with one more atom. -/
def addAtom (atom rest : Pattern) : Pattern := .apply "prime-space-add" [atom, rest]

/-- **The space of a list of atoms**, the first atom outermost. -/
def spaceOfAtoms : List Pattern → Pattern
  | [] => emptySpace
  | atom :: atoms => addAtom atom (spaceOfAtoms atoms)

/-- The variable atom of an index. -/
def variableAtom (index : Pattern) : Pattern := .apply "prime-variable" [index]

mutual
  /-- **The atoms stored in a space term**, in order.  A pattern that is no
  space stores nothing. -/
  def storedAtoms : Pattern → List Pattern
    | .apply label arguments =>
        if label = "prime-space-add" then storedAtomsList arguments else []
    | _ => []

  /-- The atoms stored by the two arguments of an addition. -/
  def storedAtomsList : List Pattern → List Pattern
    | [atom, rest] => atom :: storedAtoms rest
    | _ => []
end

@[simp] theorem storedAtoms_emptySpace : storedAtoms emptySpace = [] := by
  simp [emptySpace, storedAtoms]

@[simp] theorem storedAtoms_addAtom (atom rest : Pattern) :
    storedAtoms (addAtom atom rest) = atom :: storedAtoms rest := by
  simp [addAtom, storedAtoms, storedAtomsList]

/-- **A space stores the atoms it was built from.** -/
theorem storedAtoms_spaceOfAtoms (atoms : List Pattern) :
    storedAtoms (spaceOfAtoms atoms) = atoms := by
  induction atoms with
  | nil => simp [spaceOfAtoms]
  | cons atom atoms ih => simp [spaceOfAtoms, ih]

/-- **Negative**: an atom stores nothing. -/
theorem storedAtoms_unitAtom : storedAtoms unitAtom = [] := by decide

theorem emptySpace_wellSorted (bound : List TypeExpr) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Space") emptySpace :=
  wellSorted_apply_zero (lang := probeWithSpace) (label := "prime-space-empty") (by decide)

theorem addAtom_wellSorted {bound : List TypeExpr} {atom rest : Pattern}
    (atomSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Atom")
      atom)
    (restSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Space")
      rest) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Space")
      (addAtom atom rest) :=
  wellSorted_apply_two (lang := probeWithSpace) (label := "prime-space-add") (firstName := "atom")
    (secondName := "rest") (by decide) atomSorted restSorted

/-- **The space of a list of atoms is a term of the sort `Space`.** -/
theorem spaceOfAtoms_wellSorted {bound : List TypeExpr} :
    ∀ {atoms : List Pattern},
      (∀ atom ∈ atoms, OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound
        (.base "Atom") atom) →
      OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Space")
        (spaceOfAtoms atoms)
  | [], _ => emptySpace_wellSorted bound
  | atom :: _, sorted =>
      addAtom_wellSorted (sorted atom (List.mem_cons_self ..))
        (spaceOfAtoms_wellSorted fun other member => sorted other (List.mem_cons_of_mem _ member))

theorem variableAtom_wellSorted {bound : List TypeExpr} {index : Pattern}
    (sorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Atom")
      index) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Atom")
      (variableAtom index) :=
  wellSorted_apply_one (lang := probeWithSpace) (label := "prime-variable") (name := "index")
    (by decide) sorted

/-- The interface of the closed spaces. -/
def closedSpace : Contexts.Interface := ⟨.base "Space", []⟩

/-- The space of the unit atom and then the first numeral. -/
def twoAtomSpace : Contexts.Term probeWithSpace closedSpace :=
  ⟨spaceOfAtoms [unitAtom, numeral 1], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The same two atoms, added in the other order. -/
def swappedSpace : Contexts.Term probeWithSpace closedSpace :=
  ⟨spaceOfAtoms [numeral 1, unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **A space is a list, not a bag**: two spaces with the same atoms in
another order are apart, for every evaluator. -/
theorem spaceOfAtoms_apart (base : BasePremiseEvaluator) :
    ¬ (termSetoid base probeWithSpace closedSpace).r twoAtomSpace swappedSpace := by
  intro related
  have same := probeWithSpace_quoteDropOnly.contract_eq related
  revert same
  decide

/-! ## Closed requests, and a closed reduction of three steps -/

/-- An evaluation request for the unit atom at the empty space: a closed
request. -/
def closedEvaluationTerm : Contexts.Term probeWithSpace closedProcess :=
  ⟨.apply "zero-evaluate" [emptySpace, unitAtom],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The Need for the unit atom at the empty space. -/
def closedNeedTerm : Contexts.Term probeWithSpace closedProcess :=
  ⟨needRequest emptySpace unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- Its answer. -/
def closedNeedAnswerTerm : Contexts.Term probeWithSpace closedProcess :=
  ⟨.apply "prime-need-answer" [unitAtom, .apply "prime-receipt" [unitAtom]],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The evaluation answer. -/
def closedEvaluationAnswerTerm : Contexts.Term probeWithSpace closedProcess :=
  ⟨.apply "zero-evaluate-answer" [unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The steps of the probe are steps of the extension, under an evaluator
that does not read the language. -/
theorem language_step_probeWithSpace {base : BasePremiseEvaluator}
    (blind : ∀ bindings premise, base language bindings premise = base probeWithSpace bindings premise)
    {source target : Pattern} (step : Step base language source target) :
    Step base probeWithSpace source target :=
  Step.transport (fun _ member => List.mem_append_left [runRewrite] member)
    (fun _ _ premise _ bindings _ answered => blind bindings premise ▸ answered) step

/-- **A reduction of three steps between closed terms**, under the evaluator
that answers every Need: the request enters Need, Need is answered, and the
answer returns.  In the probe no reduction between closed terms has two
steps. -/
theorem space_closed_steps_three :
    (contextTheory answeringEvaluator spacePresentation).Steps 3 closedEvaluationTerm
      closedEvaluationAnswerTerm :=
  .succ ⟨closedEvaluationTerm, closedNeedTerm, Relation.EqvGen.refl _,
      language_step_probeWithSpace (fun _ _ => rfl) (evaluationDemand_step _ _ _),
      Relation.EqvGen.refl _⟩
    (.succ ⟨closedNeedTerm, closedNeedAnswerTerm, Relation.EqvGen.refl _,
        language_step_probeWithSpace (fun _ _ => rfl) (need_step _ _), Relation.EqvGen.refl _⟩
      (.succ ⟨closedNeedAnswerTerm, closedEvaluationAnswerTerm, Relation.EqvGen.refl _,
          language_step_probeWithSpace (fun _ _ => rfl) (needReturn_step _ _ _),
          Relation.EqvGen.refl _⟩ (.zero _)))

/-! ## The rank -/

/-- **For every evaluator a transition of the extension lowers the rank of
the probe, or goes from a run to a run.** -/
theorem space_termStep_lowers_or_runs {base : BasePremiseEvaluator}
    {interface : Contexts.Interface} {source target : Contexts.Term probeWithSpace interface}
    (step : TermStep base probeWithSpace source target) :
    patternRank target.1 < patternRank source.1 ∨
      (head? (contract source.1) = some "prime-run" ∧
        head? (contract target.1) = some "prime-run") :=
  runRules_termStep_lowers_or_runs probeWithSpace_quoteDropOnly probeWithSpace_rewrites step

/-- **Under the evaluator that answers nothing the extension has a rank**:
closed requests alone give no computation. -/
def silentSpaceRank : (contextTheory silentEvaluator spacePresentation).Rank :=
  silentRankOfRules spacePresentation probeWithSpace_quoteDropOnly probeWithSpace_rewrites

/-- So under that evaluator it hosts no theory given by a table, on terms. -/
theorem silentSpace_hosts_no_tabular_terms {source : ContextTheory.{0}}
    (tabular : TabularTheory source) (interface : source.Interface) :
    ¬ HostedBy (source.gslt interface).termsAlone
      (contextTheory silentEvaluator spacePresentation) :=
  not_hostedBy_tabular_terms_of_rank silentSpaceRank tabular interface

/-- **Under every evaluator that respects the static equivalence the
extension is finitely branching at every interface.** -/
theorem spacePresentation_finitelyBranching {base : BasePremiseEvaluator}
    (respects : RespectsStatics base probeWithSpace) (interface : Contexts.Interface) :
    FinitelyBranching ((contextTheory base spacePresentation).gslt interface) :=
  fun term => finite_reducts_of_respectsStatics probeWithSpace_quoteDropOnly
    probeWithSpace_quoteDropSorted probeWithSpace_rewrites respects term

#print axioms probeWithSpace_validate
#print axioms probeWithSpace_quoteDropOnly
#print axioms storedAtoms_spaceOfAtoms
#print axioms spaceOfAtoms_wellSorted
#print axioms spaceOfAtoms_apart
#print axioms space_closed_steps_three
#print axioms space_termStep_lowers_or_runs
#print axioms silentSpaceRank
#print axioms silentSpace_hosts_no_tabular_terms
#print axioms spacePresentation_finitelyBranching

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
