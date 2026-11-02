import Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles.ProbeStatics
import Mettapedia.Logic.HostingStyles.ReductionRank
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# The reduction of the candidate presentation

The probe (`PrimeCandidates.LanguageDef.language`) has six rewrites and no
rewrite with a congruence premise.  This module reads its reduction off those
six rules, for every evaluator of the premises.

* **A step fires one rule at the root** (`exists_rule_of_step`), and each of
  the six rules goes from one head to another (`probe_step_heads`).  The
  heads form a graph without cycle whose longest path has three edges.
* So **the probe has a rank** (`probeRank`), at most three everywhere
  (`probeRank_le`): its reduction is terminating (`probe_terminating`) and no
  reduction has four steps (`probe_not_steps_four`).
* **Only the sort `Process` reduces** (`probe_step_type`): the interfaces of
  atoms, names, receipts and of every other type are static
  (`probe_static_of_ne_process`).
* **The sort `Space` has no constructor** (`language_space_no_constructor`),
  like the sort `Alternatives`.  A request for a query, an evaluation, a Need
  or the evaluation of a name takes a space, so no closed term is a request
  (`not_hasType_space`).  At a closed interface the one transition is the
  return of a Need answer (`probe_closed_step`), and no reduction has two
  steps (`probe_closed_not_steps_two`).
* The bound of three is attained under an evaluator that answers every Need
  (`probe_steps_three`).
* **The demand of a name depends on how the name is written**
  (`probe_demand_branches`): `prime-evaluate-name space (prime-quote atom)`
  reduces to the Need for `atom` and, through the equation of quotation and
  dropping, to the Need for `prime-drop (prime-quote atom)`; the two are
  apart.
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
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
  (applyBindingsForRule_eq_syntactic applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## A step fires one rule at the root -/

/-- **A step fires a rule at the root**: the source matches the left side of
the rule, its premises hold, and the target is its right side under the
final bindings. -/
theorem exists_rule_of_step {base : BasePremiseEvaluator} {lang : LanguageDef}
    {source target : Pattern} (step : Step base lang source target) :
    ∃ rule ∈ lang.rewrites, ∃ (fuel : Nat) (initial final : Bindings),
      initial ∈ matchPattern rule.left source ∧
        PremisesAt base lang fuel initial rule.premises final ∧
          applyRuleBindings rule final = target := by
  obtain ⟨_, bounded⟩ := step
  cases bounded with
  | rule member matched premises applied =>
      rw [matchPatternForRule_eq_syntactic] at matched
      rw [applyBindingsForRule_eq_syntactic] at applied
      exact ⟨_, member, _, _, _, matched, premises, applied⟩

/-- The head of a pattern that is an application. -/
def head? : Pattern → Option String
  | .apply label _ => some label
  | _ => none

theorem eq_apply_of_head? {pattern : Pattern} {label : String} (head : head? pattern = some label) :
    ∃ arguments, pattern = .apply label arguments := by
  cases pattern with
  | apply other arguments =>
      obtain rfl : other = label := Option.some.inj head
      exact ⟨arguments, rfl⟩
  | _ => cases head

/-- What matches an application has its head. -/
theorem head?_of_matched {label : String} {parameters : List Pattern} {source : Pattern}
    {bindings : Bindings} (matched : bindings ∈ matchPattern (.apply label parameters) source) :
    head? source = some label := by
  cases matchPattern_sound matched with
  | apply _ _ => rfl

/-- The instance of a right side that is an application has its head. -/
theorem head?_applyRuleBindings (rule : RewriteRule) (final : Bindings) {label : String}
    {arguments : List Pattern} (right : rule.right = .apply label arguments) :
    head? (applyRuleBindings rule final) = some label := by
  rw [applyRuleBindings, right]
  rfl

/-! ## The six rewrites of the probe, by their heads -/

/-- The rewrites of the probe, each as the head of its left side and the head
of its right side. -/
def probeEdges : List (String × String) :=
  [("zero-query", "zero-query-answer"), ("zero-evaluate", "zero-evaluate-answer"),
    ("zero-evaluate", "prime-need"), ("prime-need", "prime-need-answer"),
    ("prime-need-answer", "zero-evaluate-answer"), ("prime-evaluate-name", "prime-need")]

/-- **Every step of the probe goes along one of its six edges.** -/
theorem probe_step_heads {base : BasePremiseEvaluator} {source target : Pattern}
    (step : Step base language source target) :
    ∃ edge ∈ probeEdges, head? source = some edge.1 ∧ head? target = some edge.2 := by
  obtain ⟨rule, member, _, initial, final, matched, _, rfl⟩ := exists_rule_of_step step
  change rule ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite,
    needRewrite, needReturnRewrite, reflectedDemandRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
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

/-! ## The rank -/

/-- The rank of a head: the number of edges of the longest path that starts
at it. -/
def headRank (label : String) : Nat :=
  if label = "zero-evaluate" ∨ label = "prime-evaluate-name" then 3
  else if label = "prime-need" then 2
  else if label = "prime-need-answer" ∨ label = "zero-query" then 1
  else 0

/-- **The rank of a pattern**: the rank of the head of its contraction. -/
def patternRank (pattern : Pattern) : Nat :=
  match head? (contract pattern) with
  | some label => headRank label
  | none => 0

theorem headRank_le (label : String) : headRank label ≤ 3 := by
  unfold headRank
  split_ifs <;> omega

theorem patternRank_le (pattern : Pattern) : patternRank pattern ≤ 3 := by
  unfold patternRank
  cases head? (contract pattern) with
  | none => exact Nat.zero_le _
  | some label => exact headRank_le label

theorem patternRank_congr {first second : Pattern} (same : contract first = contract second) :
    patternRank first = patternRank second := by
  unfold patternRank
  rw [same]

/-- The rank of an application whose head is not quotation is the rank of
its head. -/
theorem patternRank_of_head? {pattern : Pattern} {label : String}
    (head : head? pattern = some label) (other : label ≠ "prime-quote") :
    patternRank pattern = headRank label := by
  obtain ⟨arguments, rfl⟩ := eq_apply_of_head? head
  unfold patternRank
  rw [contract_apply_of_ne other]
  rfl

/-- **Every step of the probe lowers the rank.** -/
theorem probe_step_lowers {base : BasePremiseEvaluator} {source target : Pattern}
    (step : Step base language source target) : patternRank target < patternRank source := by
  obtain ⟨edge, member, sourceHead, targetHead⟩ := probe_step_heads step
  simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [patternRank_of_head? sourceHead (by decide), patternRank_of_head? targetHead (by decide)] <;>
    decide

/-- Every transition of the generated context theory lowers the rank. -/
theorem probe_termStep_lowers {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {source target : Contexts.Term language interface}
    (step : TermStep base language source target) :
    patternRank target.1 < patternRank source.1 := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  rw [patternRank_congr (language_quoteDropOnly.contract_eq before),
    ← patternRank_congr (language_quoteDropOnly.contract_eq after)]
  exact probe_step_lowers fired

/-- **The probe has a rank**, for every evaluator of its premises. -/
def probeRank (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).Rank where
  rank := fun term => patternRank term.1
  lowers := fun step => probe_termStep_lowers step

/-- **The rank of the probe is at most three.** -/
theorem probeRank_le (base : BasePremiseEvaluator)
    {interface : (contextTheory base queryFirstCandidatePresentation).Interface}
    (term : (contextTheory base queryFirstCandidatePresentation).Term interface) :
    (probeRank base).rank term ≤ 3 :=
  patternRank_le term.1

/-- **The reduction of the probe is terminating.** -/
theorem probe_terminating (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).Terminating :=
  (probeRank base).terminating

/-- **No reduction of the probe has four steps.** -/
theorem probe_not_steps_four (base : BasePremiseEvaluator)
    {interface : (contextTheory base queryFirstCandidatePresentation).Interface}
    {term final : (contextTheory base queryFirstCandidatePresentation).Term interface} :
    ¬ (contextTheory base queryFirstCandidatePresentation).Steps 4 term final := by
  intro steps
  have counted := (probeRank base).steps_le steps
  have top := probeRank_le base term
  omega

/-! ## Only the sort `Process` reduces -/

/-- The head of every rewrite is a constructor of the sort `Process`. -/
theorem probeEdges_process :
    ∀ rule ∈ language.terms, ∀ edge ∈ probeEdges, rule.label = edge.1 → rule.category = "Process" := by
  decide

/-- **A term that reduces is a process.** -/
theorem probe_step_type {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {source target : Contexts.Term language interface}
    (step : TermStep base language source target) : interface.type = .base "Process" := by
  obtain ⟨redex, contractum, _, fired, _⟩ := step
  obtain ⟨edge, member, sourceHead, _⟩ := probe_step_heads fired
  obtain ⟨arguments, shape⟩ := eq_apply_of_head? sourceHead
  have typed := redex.2.1
  rw [shape] at typed
  obtain ⟨rule, declared, label, type⟩ := declared_constructor_of_hasType_apply typed
  rw [type, probeEdges_process rule declared edge member label]

/-- **Every interface of another type is static**: atoms, names and receipts
do not reduce. -/
theorem probe_static_of_ne_process (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (other : interface.type ≠ .base "Process")
    (source target : (contextTheory base queryFirstCandidatePresentation).Term interface) :
    ¬ (contextTheory base queryFirstCandidatePresentation).rewrites source target :=
  fun step => other (probe_step_type step)

/-! ## The sort `Space` has no term, so no closed term is a request -/

/-- **The sort `Space` has no constructor.** -/
theorem language_space_no_constructor :
    language.terms.all (fun term => !(term.category == "Space")) = true := by
  decide

theorem language_category_ne_space : ∀ rule ∈ language.terms, rule.category ≠ "Space" := by
  decide

theorem language_no_bareCollection :
    ∀ rule ∈ language.terms, usesBareCollection? rule = false := by
  decide

/-- **No closed object pattern has the sort `Space`.** -/
theorem not_hasType_space {pattern : Pattern}
    (typed : HasType language FreeTypeContext.empty [] pattern (.base "Space"))
    (object : isObjectPattern pattern = true) : False := by
  generalize same : TypeExpr.base "Space" = type at typed
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | constructor member _ _ =>
      exact language_category_ne_space _ member (TypeExpr.base.inj same).symm
  | lambda _ => cases same
  | multiLambda _ => cases same
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases same
  | collectionConstructor member parameters _ =>
      have bare := (usesBareCollection?_eq_true_iff _).mpr ⟨_, _, _, parameters⟩
      rw [language_no_bareCollection _ member] at bare
      cases bare

/-- The four requests take a space first. -/
theorem language_request_params :
    ∀ rule ∈ language.terms,
      rule.label ∈ ["zero-query", "zero-evaluate", "prime-need", "prime-evaluate-name"] →
        rule.params.head? = some (.simple "space" (.base "Space")) := by
  decide

/-- A typed application of a declared constructor has typed arguments. -/
theorem hasType_apply_inv {lang : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType lang free bound (.apply label arguments) type) :
    ∃ rule ∈ lang.terms, rule.label = label ∧
      ArgumentsHaveTypes lang free bound arguments rule.params := by
  cases typed with
  | constructor member _ argumentsTyped => exact ⟨_, member, rfl, argumentsTyped⟩

/-- **No closed object pattern is a request.** -/
theorem not_hasType_request {label : String} {arguments : List Pattern} {type : TypeExpr}
    (request : label ∈ ["zero-query", "zero-evaluate", "prime-need", "prime-evaluate-name"])
    (typed : HasType language FreeTypeContext.empty [] (.apply label arguments) type)
    (object : isObjectPattern (.apply label arguments) = true) : False := by
  obtain ⟨rule, declared, rfl, argumentsTyped⟩ := hasType_apply_inv typed
  have first := language_request_params rule declared request
  generalize rule.params = parameters at argumentsTyped first
  cases argumentsTyped with
  | nil => cases first
  | cons _ expected argumentTyped _ =>
      obtain rfl := Option.some.inj first
      obtain rfl := Option.some.inj expected
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
      exact not_hasType_space argumentTyped object.1

/-- **At a closed interface the one transition is the return of a Need
answer.** -/
theorem probe_closed_step {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    (closed : interface.stage = []) {source target : Contexts.Term language interface}
    (step : TermStep base language source target) :
    patternRank source.1 = 1 ∧ patternRank target.1 = 0 := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  rw [patternRank_congr (language_quoteDropOnly.contract_eq before),
    ← patternRank_congr (language_quoteDropOnly.contract_eq after)]
  obtain ⟨edge, member, sourceHead, targetHead⟩ := probe_step_heads fired
  obtain ⟨arguments, shape⟩ := eq_apply_of_head? sourceHead
  have typed := redex.2.1
  have object := redex.2.2.2.1
  rw [shape] at typed object
  rw [closed] at typed
  simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (not_hasType_request (by decide) typed object).elim
  · exact (not_hasType_request (by decide) typed object).elim
  · exact (not_hasType_request (by decide) typed object).elim
  · exact (not_hasType_request (by decide) typed object).elim
  · exact ⟨by rw [patternRank_of_head? sourceHead (by decide)]; decide,
      by rw [patternRank_of_head? targetHead (by decide)]; decide⟩
  · exact (not_hasType_request (by decide) typed object).elim

/-- **No reduction between closed terms has two steps.** -/
theorem probe_closed_not_steps_two (base : BasePremiseEvaluator) {interface : Contexts.Interface}
    (closed : interface.stage = [])
    {term final : (contextTheory base queryFirstCandidatePresentation).Term interface} :
    ¬ (contextTheory base queryFirstCandidatePresentation).Steps 2 term final := by
  intro steps
  cases steps with
  | succ first rest =>
      cases rest with
      | succ second _ =>
          have ended := (probe_closed_step closed first).2
          have started := (probe_closed_step closed second).1
          omega

/-! ## The return of a Need answer: the one closed transition -/

/-- The unit atom. -/
def unitAtom : Pattern := .apply "prime-unit" []

/-- The interface of the closed processes. -/
def closedProcess : Contexts.Interface := ⟨.base "Process", []⟩

/-- A Need answer for the unit atom, with the receipt rooted at it. -/
def needAnswerTerm : Contexts.Term language closedProcess :=
  ⟨.apply "prime-need-answer" [unitAtom, .apply "prime-receipt" [unitAtom]],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The evaluation answer it returns to. -/
def evaluationAnswerTerm : Contexts.Term language closedProcess :=
  ⟨.apply "zero-evaluate-answer" [unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- A Need answer returns to the evaluation answer, in one step. -/
theorem needReturn_step (base : BasePremiseEvaluator) (answer receipt : Pattern) :
    Step base language (.apply "prime-need-answer" [answer, receipt])
      (.apply "zero-evaluate-answer" [answer]) := by
  refine ⟨1, .rule (rule := needReturnRewrite)
    (initialBindings := [("receipt", receipt), ("answer", answer)]) (by simp [language]) ?_
    (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, needReturnRewrite, matchPattern, matchArgs,
      mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [needReturnRewrite, MeTTaZero.evaluationAnswerPattern, applyBindings]

/-- **Positive**: the probe has a transition between closed terms, for every
evaluator of its premises. -/
theorem probe_closed_transition (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).rewrites needAnswerTerm
      evaluationAnswerTerm :=
  ⟨needAnswerTerm, evaluationAnswerTerm, Relation.EqvGen.refl _, needReturn_step base _ _,
    Relation.EqvGen.refl _⟩

/-! ## The demand of a name depends on how the name is written -/

/-- The interface of the processes that mention one space. -/
def openProcess : Contexts.Interface := ⟨.base "Process", [.base "Space"]⟩

/-- `prime-evaluate-name space name`. -/
def evaluateName (space name : Pattern) : Pattern := .apply "prime-evaluate-name" [space, name]

/-- `prime-need space subject`. -/
def needRequest (space subject : Pattern) : Pattern := .apply "prime-need" [space, subject]

/-- The evaluation of a quoted atom demands the atom, in one step. -/
theorem reflectedDemand_step (base : BasePremiseEvaluator) (space subject : Pattern) :
    Step base language (evaluateName space (quoted subject)) (needRequest space subject) := by
  refine ⟨1, .rule (rule := reflectedDemandRewrite)
    (initialBindings := [("subject", subject), ("space", space)]) (by simp [language]) ?_
    (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, reflectedDemandRewrite, evaluateName, quoted,
      matchPattern, matchArgs, mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [reflectedDemandRewrite, needRequest, applyBindings]

/-- **The quotation of a dropping is equal to what was dropped**, in every
context, in a language with that equation. -/
theorem quoteDrop_contextStep (base : BasePremiseEvaluator) {lang : LanguageDef}
    (authored : quoteDropEquation ∈ lang.equations) (context : OneHoleContext)
    (name : Pattern) :
    EquationContextStep base lang (context.fill (quoted (dropped name))) (context.fill name) := by
  refine .inContext context (.inl ⟨0, .forward (equation := quoteDropEquation)
    (initialBindings := [("name", name)]) authored
    (Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl) ?_ (.nil _) ?_⟩)
  · simp [quoteDropEquation, quoted, dropped, matchPattern, matchArgs, mergeBindings]
  · simp [quoteDropEquation, applyBindings]

/-- The evaluation of the quoted unit atom, at one space. -/
def demandTerm : Contexts.Term language openProcess :=
  ⟨evaluateName (.bvar 0) (quoted unitAtom), checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The same name, written as the quotation of the dropping of itself. -/
def demandTermLong : Contexts.Term language openProcess :=
  ⟨evaluateName (.bvar 0) (quoted (dropped (quoted unitAtom))),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The Need for the unit atom. -/
def needUnitTerm : Contexts.Term language openProcess :=
  ⟨needRequest (.bvar 0) unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The Need for the dropping of the quoted unit atom. -/
def needDroppedTerm : Contexts.Term language openProcess :=
  ⟨needRequest (.bvar 0) (dropped (quoted unitAtom)),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The two ways of writing the name are equal. -/
theorem demandTermLong_equiv (base : BasePremiseEvaluator) :
    (termSetoid base language openProcess).r demandTermLong demandTerm :=
  .rel _ _ (quoteDrop_contextStep base (lang := language)
    (language_quoteDropOnly.equations ▸ List.mem_singleton.mpr rfl)
    (.apply "prime-evaluate-name" [.bvar 0] .hole []) (quoted unitAtom))

/-- The two Needs are apart. -/
theorem needUnitTerm_apart (base : BasePremiseEvaluator) :
    ¬ (termSetoid base language openProcess).r needUnitTerm needDroppedTerm := by
  intro related
  have same := language_quoteDropOnly.contract_eq related
  revert same
  decide

/-- **The demand of a name depends on how the name is written**: one term has
two transitions with results that are apart, for every evaluator of the
premises. -/
theorem probe_demand_branches (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).rewrites demandTerm needUnitTerm ∧
      (contextTheory base queryFirstCandidatePresentation).rewrites demandTerm needDroppedTerm ∧
        ¬ ((contextTheory base queryFirstCandidatePresentation).equations openProcess).r
          needUnitTerm needDroppedTerm :=
  ⟨⟨demandTerm, needUnitTerm, Relation.EqvGen.refl _, reflectedDemand_step base _ _,
      Relation.EqvGen.refl _⟩,
    ⟨demandTermLong, needDroppedTerm, Relation.EqvGen.symm _ _ (demandTermLong_equiv base),
      reflectedDemand_step base _ _, Relation.EqvGen.refl _⟩,
    needUnitTerm_apart base⟩

/-! ## The bound of three steps is attained -/

/-- An evaluator of the premises that answers every Need with its subject,
under the receipt rooted at it, and answers no other relation. -/
def answeringEvaluator : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "CandidateNeed" [_, subject, .fvar answer, .fvar receipt] =>
      [(receipt, .apply "prime-receipt" [applyBindings bindings subject]) ::
        (answer, applyBindings bindings subject) :: bindings]
  | _ => []

/-- An evaluation request enters Need, in one step. -/
theorem evaluationDemand_step (base : BasePremiseEvaluator) (space subject : Pattern) :
    Step base language (.apply "zero-evaluate" [space, subject]) (needRequest space subject) := by
  refine ⟨1, .rule (rule := evaluationDemandRewrite)
    (initialBindings := [("subject", subject), ("space", space)]) (by simp [language]) ?_
    (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, evaluationDemandRewrite,
      MeTTaZero.evaluationRequestPattern, matchPattern, matchArgs, mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [evaluationDemandRewrite, needRequest, applyBindings]

/-- Under the answering evaluator a Need is answered with its subject. -/
theorem need_step (space subject : Pattern) :
    Step answeringEvaluator language (needRequest space subject)
      (.apply "prime-need-answer" [subject, .apply "prime-receipt" [subject]]) := by
  refine ⟨1, .rule (rule := needRewrite)
    (initialBindings := [("subject", subject), ("space", space)])
    (finalBindings := [("receipt", .apply "prime-receipt" [subject]), ("answer", subject),
      ("subject", subject), ("space", space)]) (by simp [language]) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, needRewrite, needRequest, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    simp [answeringEvaluator, applyBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [needRewrite, applyBindings]

/-- An evaluation request for the unit atom, at one space. -/
def evaluationRequestTerm : Contexts.Term language openProcess :=
  ⟨.apply "zero-evaluate" [.bvar 0, unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The Need answer for the unit atom, at one space. -/
def openNeedAnswerTerm : Contexts.Term language openProcess :=
  ⟨.apply "prime-need-answer" [unitAtom, .apply "prime-receipt" [unitAtom]],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The evaluation answer for the unit atom, at one space. -/
def openEvaluationAnswerTerm : Contexts.Term language openProcess :=
  ⟨.apply "zero-evaluate-answer" [unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Positive**: under the answering evaluator the probe has a reduction of
three steps, from an evaluation request through Need to the evaluation
answer.  The bound of `probe_not_steps_four` is attained. -/
theorem probe_steps_three :
    (contextTheory answeringEvaluator queryFirstCandidatePresentation).Steps 3
      evaluationRequestTerm openEvaluationAnswerTerm :=
  .succ ⟨evaluationRequestTerm, needUnitTerm, Relation.EqvGen.refl _,
      evaluationDemand_step _ _ _, Relation.EqvGen.refl _⟩
    (.succ ⟨needUnitTerm, openNeedAnswerTerm, Relation.EqvGen.refl _, need_step _ _,
        Relation.EqvGen.refl _⟩
      (.succ ⟨openNeedAnswerTerm, openEvaluationAnswerTerm, Relation.EqvGen.refl _,
          needReturn_step _ _ _, Relation.EqvGen.refl _⟩ (.zero _)))

#print axioms probe_steps_three
#print axioms exists_rule_of_step
#print axioms probe_step_heads
#print axioms probe_step_lowers
#print axioms probeRank
#print axioms probeRank_le
#print axioms probe_terminating
#print axioms probe_not_steps_four
#print axioms probe_step_type
#print axioms probe_static_of_ne_process
#print axioms language_space_no_constructor
#print axioms not_hasType_space
#print axioms not_hasType_request
#print axioms probe_closed_step
#print axioms probe_closed_not_steps_two
#print axioms probe_closed_transition
#print axioms probe_demand_branches

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
