import Mettapedia.Logic.HostingStyles.PrimeCandidate.PresentedSteps

/-!
# Hosting by rewrites of the candidate's own: the union with the universal Turing theory

A presentation whose rewrite hands its premise to an evaluator hosts what the
evaluator hosts.  This module takes the other route.  It joins the probe, as
it is, with a presented theory whose rules are data in the term: the
universal Turing theory, four rewrites on a bag that mention no table
(`probeWithTuring`, validated: `turingPresentation`).  The four rewrites
carry no premise.

* **Under every evaluator of the premises the union hosts every Turing
  machine, on terms** (`turingMap_hosting`,
  `turingPresentation_hostOf_machineTheory`): a configuration is read as the
  bag of the configuration and the rows of the machine.  One step of the
  machine is one step of the union (`turing_steps`).  The evaluator is not
  consulted: the steps of the universal theory are steps of the union under
  every evaluator (`Step.transport_of_premiseFree`), and no rewrite of the
  probe fires on a bag.
* So under every evaluator, the one that answers nothing included, the union
  has reductions of every length and no rank (`turing_steps_every_length`,
  `turingPresentation_not_rank`).
* The static equivalence of the union is that of quotation and dropping
  together with the commutation of the members of a bag
  (`QuoteDropWithBags`).  It keeps the contraction of a pattern with the
  members of its bags in one order (`settle`, `QuoteDropWithBags.settle_eq`).
  The sorts of the machine are apart from quotation
  (`probeWithTuring_machineSorts_apart`), so a term of those sorts is equal
  only to its rearrangements.
* The map is not exhausting (`turingMap_not_exhausting`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.TuringMachine
  (Machine Configuration Transition universalTheory universal universalTerms mixConstructor
    mixConstructor_mem interiorRightRule interiorLeftRule edgeRightRule edgeLeftRule rowPattern row
    run tapeAt cell emptyCells moveTerm symbolTerm ruleContext soup description withTable TableWith
    configurationGSLT turingMachine tableWith_forward tableWith_backward universalTheory_plain
    rowTerm rowTerm_ne_term soups step_term_iff step_term_term_iff)

/-! ## The union -/

/-- **The probe together with the universal Turing theory**: the sorts, the
constructors and the rewrites of both, and the one equation of the probe. -/
def probeWithTuring : LanguageDef :=
  { language with
    name := "metta-prime-spec-probe-with-universal-machine"
    types := language.types ++ universalTheory.types
    terms := language.terms ++ universalTheory.terms
    rewrites := language.rewrites ++ universalTheory.rewrites }

theorem probeWithTuring_typeNames : probeWithTuring.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt",
      "State", "Symbol", "Cells", "Tape", "Move", "Soup"] := by
  decide

theorem probeWithTuring_labels :
    RewriteValidationCertificate.constructorLabels probeWithTuring =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "QZero", "QSucc", "SZero", "SSucc", "Empty", "Cell", "At", "Left",
        "Right", "Row", "Run", "Mix"] := by
  decide

theorem probeWithTuring_signatures :
    RewriteValidationCertificate.constructorSignatures probeWithTuring =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("QZero", 0), ("QSucc", 1),
        ("SZero", 0), ("SSucc", 1), ("Empty", 0), ("Cell", 2), ("At", 3), ("Left", 0),
        ("Right", 0), ("Row", 5), ("Run", 2), ("Mix", 1)] := by
  decide

theorem probeWithTuring_probe_checked :
    ∀ rewrite ∈ language.rewrites,
      RewriteValidationCertificate.check probeWithTuring rewrite = true := by
  intro rewrite member
  change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite,
    needRewrite, needReturnRewrite, reflectedDemandRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      probeWithTuring_typeNames, probeWithTuring_signatures, probeWithTuring_labels,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, needRewrite, evaluationDemandRewrite,
      needReturnRewrite, reflectedDemandRewrite,
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

/-- The four rewrites of the universal theory pass their rows of the
declaration gate in the union. -/
theorem probeWithTuring_universal_checked :
    ∀ rewrite ∈ universalTheory.rewrites,
      RewriteValidationCertificate.check probeWithTuring rewrite = true := by
  intro rewrite member
  change rewrite ∈ [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have checked : ∀ candidate : RewriteRule,
      (candidate = interiorRightRule ∨ candidate = interiorLeftRule) ∨
        (candidate = edgeRightRule ∨ candidate = edgeLeftRule) →
      RewriteValidationCertificate.check probeWithTuring candidate = true := by
    rintro candidate ((rfl | rfl) | (rfl | rfl))
    · simp [RewriteValidationCertificate.check,
        RewriteValidationCertificate.contextTypesCheck,
        RewriteValidationCertificate.premiseTypesCheck,
        RewriteValidationCertificate.patternDeclaredCheck,
        RewriteValidationCertificate.premisesDeclaredCheck,
        RewriteValidationCertificate.allPatternsScopedCheck,
        RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
        RewriteValidationCertificate.bindersAvoidConstructorsCheck,
        RewriteValidationCertificate.contextAvoidsConstructorsCheck,
        RewriteValidationCertificate.rightBoundCheck,
        probeWithTuring_typeNames, probeWithTuring_signatures, probeWithTuring_labels,
        interiorRightRule, rowPattern, row, run, tapeAt, cell, moveTerm, ruleContext,
        LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, TypeExpr.baseNames,
        Pattern.constructorRefs, Pattern.constructorRefsList,
        Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
    · simp [RewriteValidationCertificate.check,
        RewriteValidationCertificate.contextTypesCheck,
        RewriteValidationCertificate.premiseTypesCheck,
        RewriteValidationCertificate.patternDeclaredCheck,
        RewriteValidationCertificate.premisesDeclaredCheck,
        RewriteValidationCertificate.allPatternsScopedCheck,
        RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
        RewriteValidationCertificate.bindersAvoidConstructorsCheck,
        RewriteValidationCertificate.contextAvoidsConstructorsCheck,
        RewriteValidationCertificate.rightBoundCheck,
        probeWithTuring_typeNames, probeWithTuring_signatures, probeWithTuring_labels,
        interiorLeftRule, rowPattern, row, run, tapeAt, cell, moveTerm, ruleContext,
        LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, TypeExpr.baseNames,
        Pattern.constructorRefs, Pattern.constructorRefsList,
        Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
    · simp [RewriteValidationCertificate.check,
        RewriteValidationCertificate.contextTypesCheck,
        RewriteValidationCertificate.premiseTypesCheck,
        RewriteValidationCertificate.patternDeclaredCheck,
        RewriteValidationCertificate.premisesDeclaredCheck,
        RewriteValidationCertificate.allPatternsScopedCheck,
        RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
        RewriteValidationCertificate.bindersAvoidConstructorsCheck,
        RewriteValidationCertificate.contextAvoidsConstructorsCheck,
        RewriteValidationCertificate.rightBoundCheck,
        probeWithTuring_typeNames, probeWithTuring_signatures, probeWithTuring_labels,
        edgeRightRule, rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm,
        ruleContext, Pattern.unary,
        LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, TypeExpr.baseNames,
        Pattern.constructorRefs, Pattern.constructorRefsList,
        Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
    · simp [RewriteValidationCertificate.check,
        RewriteValidationCertificate.contextTypesCheck,
        RewriteValidationCertificate.premiseTypesCheck,
        RewriteValidationCertificate.patternDeclaredCheck,
        RewriteValidationCertificate.premisesDeclaredCheck,
        RewriteValidationCertificate.allPatternsScopedCheck,
        RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
        RewriteValidationCertificate.bindersAvoidConstructorsCheck,
        RewriteValidationCertificate.contextAvoidsConstructorsCheck,
        RewriteValidationCertificate.rightBoundCheck,
        probeWithTuring_typeNames, probeWithTuring_signatures, probeWithTuring_labels,
        edgeLeftRule, rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm,
        ruleContext, Pattern.unary,
        LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, TypeExpr.baseNames,
        Pattern.constructorRefs, Pattern.constructorRefsList,
        Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
  exact checked rewrite (by tauto)

/-- **The union passes the declaration gate.** -/
theorem probeWithTuring_validate : probeWithTuring.validate = [] := by
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
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          probeWithTuring.equations.all (LanguageDef.plainEquationOk probeWithTuring) = true)
        equation member)
  case hrewriteValid =>
    intro rewrite member
    refine RewriteValidationCertificate.validateRewrite_eq_nil_of_check (by decide +kernel) ?_
    rcases List.mem_append.mp member with inProbe | inUniversal
    · exact probeWithTuring_probe_checked rewrite inProbe
    · exact probeWithTuring_universal_checked rewrite inUniversal

/-- The union, as a presentation. -/
def turingPresentation : ValidatedLanguageDef := ⟨probeWithTuring, probeWithTuring_validate⟩

/-! ## The static equivalence: quotation and dropping, and bags -/

/-- **The static laws of a language are those of quotation and dropping and
of its bags**: its one authored equation is that of quotation and dropping,
and it declares no set and no collection algebra. -/
structure QuoteDropWithBags (lang : LanguageDef) : Prop where
  equations : lang.equations = [quoteDropEquation]
  noSets : lang.usesCollection .hashSet = false
  noAlgebra : lang.hasAlgebraDeclarations = false

/-- **Positive**: the union. -/
theorem probeWithTuring_quoteDropWithBags : QuoteDropWithBags probeWithTuring :=
  ⟨rfl, by decide, by decide⟩

/-- **Negative**: the universal theory alone authors no equation. -/
theorem universalTheory_not_quoteDropWithBags : ¬ QuoteDropWithBags universalTheory :=
  fun laws => List.cons_ne_nil _ _ laws.equations.symm

/-- The union has a bag, so its static equivalence is not that of quotation
and dropping alone. -/
theorem probeWithTuring_not_quoteDropOnly : ¬ QuoteDropOnly probeWithTuring := by
  intro only
  have bags := only.noBags
  revert bags
  decide

/-- An instance of the equation of quotation and dropping relates a pattern
and its quoted dropping, in one of the two directions. -/
theorem quoteDrop_instance {lang : LanguageDef} (equations : lang.equations = [quoteDropEquation])
    {base : BasePremiseEvaluator} {source target : Pattern}
    (authored : EquationInstance base lang source target) :
    source = quoted (dropped target) ∨ target = quoted (dropped source) := by
  obtain ⟨fuel, authored⟩ := authored
  cases authored with
  | forward member _ matched premises applied =>
      rename_i equation initial final _
      rw [equations] at member
      obtain rfl : equation = quoteDropEquation := List.mem_singleton.mp member
      have same : final = initial := by
        change PremisesAt base lang fuel initial [] final at premises
        cases premises
        rfl
      subst same
      have rebuilt := matchPattern_correct matched (by decide)
      refine .inl ?_
      rw [← rebuilt, ← applied]
      simp [quoteDropEquation, applyBindings, quoted, dropped]
  | reverse member _ matched premises applied =>
      rename_i equation initial final _
      rw [equations] at member
      obtain rfl : equation = quoteDropEquation := List.mem_singleton.mp member
      have same : final = initial := by
        change PremisesAt base lang fuel initial [] final at premises
        cases premises
        rfl
      subst same
      have bound : final = [("name", source)] := by
        simpa [quoteDropEquation, matchPattern] using matched
      subst bound
      refine .inr ?_
      rw [← applied]
      simp [quoteDropEquation, applyBindings, quoted, dropped]
  | @declared equation _ _ _ _ member notRaw _ =>
      rw [equations] at member
      obtain rfl : equation = quoteDropEquation := List.mem_singleton.mp member
      rw [readsRaw_of_none rfl] at notRaw
      cases notRaw

/-- **The contraction of a pattern, with the members of its bags in one
order.** -/
def settle (pattern : Pattern) : Pattern := normalForm none (contract pattern)

/-- Ordering the bags commutes with the contraction at the root. -/
theorem normalForm_contractRoot (label : String) (arguments : List Pattern) :
    normalForm none (contractRoot label arguments) =
      contractRoot label (arguments.map (normalForm none)) := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rcases arguments with _ | ⟨head, _ | ⟨second, rest⟩⟩
    · simp [contractRoot, normalForm, normalFormList]
    · cases head with
      | apply inner innerArguments =>
          rcases innerArguments with _ | ⟨name, _ | ⟨other, more⟩⟩
          · simp [contractRoot, normalForm, normalFormList]
          · by_cases isDrop : inner = "prime-drop"
            · subst isDrop
              simp [contractRoot, normalForm, normalFormList]
            · simp [contractRoot, normalForm, normalFormList, isDrop]
          · simp [contractRoot, normalForm, normalFormList]
      | collection kind elements tail =>
          by_cases bag : kind = .hashBag ∧ tail = none
          · simp [contractRoot, normalForm, normalFormList, bag, normalizeBag]
          · simp [contractRoot, normalForm, normalFormList, bag]
      | _ => simp [contractRoot, normalForm, normalFormList]
    · simp [contractRoot, normalForm, normalFormList]
  · simp [contractRoot, isQuote, normalForm]

theorem settle_apply (label : String) (arguments : List Pattern) :
    settle (.apply label arguments) = contractRoot label (arguments.map settle) := by
  rw [settle, contract, contractList_eq_map, normalForm_contractRoot, List.map_map]
  rfl

theorem settle_lambda (binder : Option String) (body : Pattern) :
    settle (.lambda binder body) = .lambda binder (settle body) := by
  simp [settle, contract, normalForm]

theorem settle_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    settle (.multiLambda arity binders body) = .multiLambda arity binders (settle body) := by
  simp [settle, contract, normalForm]

theorem settle_subst (body replacement : Pattern) :
    settle (.subst body replacement) = .subst (settle body) (settle replacement) := by
  simp [settle, contract, normalForm]

theorem settle_collection (kind : CollType) (elements : List Pattern) (tail : Option String) :
    settle (.collection kind elements tail) =
      if kind = .hashBag ∧ tail = none then normalizeBag none (elements.map settle)
      else .collection kind (elements.map settle) tail := by
  have mapped : (elements.map contract).map (normalForm none) = elements.map settle := by
    rw [List.map_map]
    rfl
  simp [settle, contract, normalForm, mapped]

/-- The settled form sees a context only through the settled form of what
fills its hole. -/
theorem settle_fill_congr :
    ∀ (context : OneHoleContext) {first second : Pattern}, settle first = settle second →
      settle (context.fill first) = settle (context.fill second)
  | .hole, _, _, same => same
  | .apply label before inner after, _, _, same => by
      simp only [OneHoleContext.fill, settle_apply, List.map_append, List.map_cons,
        settle_fill_congr inner same]
  | .lambda binder inner, _, _, same => by
      simp only [OneHoleContext.fill, settle_lambda, settle_fill_congr inner same]
  | .multiLambda arity binders inner, _, _, same => by
      simp only [OneHoleContext.fill, settle_multiLambda, settle_fill_congr inner same]
  | .substBody inner replacement, _, _, same => by
      simp only [OneHoleContext.fill, settle_subst, settle_fill_congr inner same]
  | .substReplacement body inner, _, _, same => by
      simp only [OneHoleContext.fill, settle_subst, settle_fill_congr inner same]
  | .collection kind before inner after tail, _, _, same => by
      simp only [OneHoleContext.fill, settle_collection, List.map_append, List.map_cons,
        settle_fill_congr inner same]

/-- **Equal patterns have one settled form**, in a language whose static laws
are those of quotation and dropping and of its bags. -/
theorem QuoteDropWithBags.settle_eq {lang : LanguageDef} (laws : QuoteDropWithBags lang)
    {base : BasePremiseEvaluator} {left right : Pattern}
    (equivalent : EquationEquiv base lang left right) : settle left = settle right := by
  apply equationEquiv_invariant settle (fun context _ _ same => settle_fill_congr context same) _
    equivalent
  rintro source target (authored | derived)
  · rcases quoteDrop_instance laws.equations authored with rfl | rfl
    · rw [settle, contract_quoted_dropped]
      rfl
    · rw [settle, settle, contract_quoted_dropped]
  · cases derived with
    | bagPerm _ _ permutation =>
        rw [settle_collection, settle_collection, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
        exact normalizeBag_perm none (permutation.map _)
    | setPerm declaration typed _ =>
        have uses := usesCollection_eq_true_of_collectionTypedAt declaration typed
        rw [laws.noSets] at uses
        cases uses
    | setDedup declaration typed =>
        have uses := usesCollection_eq_true_of_collectionTypedAt declaration typed
        rw [laws.noSets] at uses
        cases uses
    | flatten algebraRule _ _ =>
        exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false laws.noAlgebra algebraRule).elim
    | singleton algebraRule _ _ =>
        exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false laws.noAlgebra algebraRule).elim
    | unitElim algebraRule _ _ =>
        exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false laws.noAlgebra algebraRule).elim
    | emptyUnit algebraRule _ _ =>
        exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false laws.noAlgebra algebraRule).elim

/-- **Negative**: the settled form tells two bags of different members
apart, so they are not equal. -/
theorem settle_separates :
    settle (soup [unitAtom]) ≠ settle (soup [unitAtom, unitAtom]) := by
  intro same
  rw [soup, soup, settle_collection, settle_collection, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
    at same
  simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true] at same
  have lengths := congrArg List.length same
  simp at lengths

/-! ## The sorts of the machine are apart from quotation -/

/-- The sorts of the universal Turing theory. -/
def machineSorts : List String := ["State", "Symbol", "Cells", "Tape", "Move", "Soup"]

/-- **No constructor of a sort of the machine is quotation, and each takes
arguments of those sorts**: a term of these sorts contains no quotation. -/
theorem probeWithTuring_machineSorts_apart : ApartFromQuotation probeWithTuring machineSorts := by
  unfold ApartFromQuotation machineSorts
  decide

/-- The constructors of the universal theory are constructors of the union. -/
def universalIntoUnion : SignatureMorphism universal turingPresentation where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := fun declaration member => by
    rw [mapTypeDecl_id]
    exact List.mem_append_right language.types member
  mapsTerms := fun rule member => by
    rw [mapGrammarRule_id]
    exact List.mem_append_right language.terms member

/-- A pattern typed in the universal theory is typed in the union. -/
theorem hasType_union {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} (typed : HasType universalTheory free bound pattern type) :
    HasType probeWithTuring free bound pattern type := by
  have mapped := typed.mapSignature universalIntoUnion
  have moved : HasType turingPresentation.language free bound pattern type := by
    simpa only [universalIntoUnion, mapPattern_id, mapTypeExpr_id,
      show mapTypeExpr LanguageDefSymbolMap.id = id from funext mapTypeExpr_id,
      FreeTypeContext.map_id, List.map_id] using mapped
  exact moved

/-- **A term of the sort of bags is its own contraction**, in the union. -/
theorem contract_of_soupTerm (term : Contexts.Term probeWithTuring soups) :
    contract term.1 = term.1 :=
  contract_of_hasType probeWithTuring_machineSorts_apart term.2.1 (by decide) term.2.2.2.1

/-! ## Bags of the rows of a machine and a configuration, in the union -/

theorem tableWith_members_fixed {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members) :
    members.map (normalForm none) = members := by
  have fixed : members.map (normalForm none) = members.map id :=
    List.map_congr_left fun member inMembers =>
      (holds.constructorTerm member inMembers).normalForm_eq none
  rw [fixed, List.map_id]

/-- Two bags of rows and a configuration with one normal form hold one
configuration. -/
theorem configuration_eq_of_normalForm_eq {machine : Machine} {first second : Configuration}
    {members others : List Pattern} (holds : TableWith machine first.term members)
    (othersHold : TableWith machine second.term others)
    (same : normalForm none (soup members) = normalForm none (soup others)) : first = second := by
  rw [soup, soup, normalForm_bag, normalForm_bag, tableWith_members_fixed holds,
    tableWith_members_fixed othersHold] at same
  simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true] at same
  have perm : (first.term :: description machine).Perm (second.term :: description machine) :=
    holds.symm.trans (((sortPatterns_perm members).symm.trans
      (same ▸ sortPatterns_perm others)).trans othersHold)
  rcases List.mem_cons.mp (perm.mem_iff.mp (List.mem_cons_self ..)) with equal | inTable
  · exact Configuration.term_injective equal
  · obtain ⟨entry, -, isEntry⟩ := List.mem_map.mp inTable
    exact absurd isEntry (rowTerm_ne_term _ _)

/-- A bag with the normal form of a bag of rows and a configuration is such
a bag. -/
theorem tableWith_of_normalForm_eq {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members)
    {elements : List Pattern} {tail : Option String}
    (same : normalForm none (soup members) =
      normalForm none (.collection .hashBag elements tail)) :
    ∃ others, Pattern.collection .hashBag elements tail = soup others ∧
      TableWith machine configuration.term others := by
  rw [soup, normalForm_bag, tableWith_members_fixed holds] at same
  cases tail with
  | some name => simp [normalForm, normalizeBag] at same
  | none =>
      rw [normalForm_bag] at same
      simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true] at same
      have images : (elements.map (normalForm none)).Perm members :=
        ((sortPatterns_perm _).symm.trans (same ▸ sortPatterns_perm members))
      have elementsFixed : elements.map (normalForm none) = elements := by
        have fixed : elements.map (normalForm none) = elements.map id :=
          List.map_congr_left fun element inElements =>
            ((holds.constructorTerm _
              (images.mem_iff.mp (List.mem_map_of_mem inElements))).eq_of_normalForm_eq
                element rfl).symm
        rw [fixed, List.map_id]
      rw [elementsFixed] at images
      exact ⟨elements, rfl, images.trans holds⟩

/-- The bag of the rows of a machine and a configuration is a term of the
union. -/
theorem tableWith_unionSorted {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members) :
    OpenPatternWellSorted probeWithTuring FreeTypeContext.empty soups.stage soups.type
      (soup members) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := holds.sorted
  exact ⟨hasType_union typed, canonical, object, scopeSafe⟩

/-- **The image of a configuration**: the bag of the configuration and the
rows of the machine, as a term of the union. -/
def unionTableTerm (machine : Machine) (configuration : Configuration) :
    Contexts.Term probeWithTuring soups :=
  ⟨withTable machine configuration.term,
    tableWith_unionSorted (machine := machine) (configuration := configuration)
      (List.Perm.refl _)⟩

/-- Two bags of the same rows and the same configuration are equal in the
union: one instance of the commutation of the members. -/
theorem union_bag_equiv (base : BasePremiseEvaluator) {machine : Machine}
    {configuration : Configuration} {members others : List Pattern}
    (holds : TableWith machine configuration.term members)
    (othersHold : TableWith machine configuration.term others)
    {first second : Contexts.Term probeWithTuring soups} (firstShape : first.1 = soup members)
    (secondShape : second.1 = soup others) :
    (termSetoid base probeWithTuring soups).r first second := by
  refine Relation.EqvGen.rel _ _ ?_
  show EquationContextStep base probeWithTuring first.1 second.1
  rw [firstShape, secondShape]
  exact EquationContextStep.inContext .hole (Or.inr (DerivedInstance.bagPerm_of_sorted
    (category := mixConstructor.category)
    ⟨FreeTypeContext.empty, [], (tableWith_unionSorted holds).1⟩ (holds.trans othersHold.symm)))

/-- A step of the union by a rule of the universal theory is a step of the
universal theory: the rule carries no premise. -/
theorem universal_step_of_rule {base : BasePremiseEvaluator} {rule : RewriteRule}
    (member : rule ∈ universalTheory.rewrites) {source target : Pattern} {fuel : Nat}
    {initial final : Bindings} (matched : initial ∈ matchPattern rule.left source)
    (premises : PremisesAt base probeWithTuring fuel initial rule.premises final)
    (applied : applyRuleBindings rule final = target) :
    Step TuringMachine.base universalTheory source target := by
  have free := (universalTheory_plain rule member).1
  rw [free] at premises
  cases premises
  refine ⟨1, .rule (initialBindings := initial) (finalBindings := initial) member ?_ ?_ ?_⟩
  · rw [matchPatternForRule_eq_syntactic]
    exact matched
  · rw [free]
    exact .nil _
  · rw [applyBindingsForRule_eq_syntactic]
    exact applied

/-! ## The hosting map -/

theorem unionTableTerm_resp (base : BasePremiseEvaluator) (machine : Machine)
    {first second : Configuration}
    (same : (configurationGSLT machine).equations.r first second) :
    (termSetoid base probeWithTuring soups).r (unionTableTerm machine first)
      (unionTableTerm machine second) := by
  have equal : first = second := same
  rw [equal]

/-- **A machine, in the union**: a configuration is read as the bag of the
configuration and the rows of the machine. -/
def turingMap (base : BasePremiseEvaluator) (machine : Machine) :
    ContextMap (configurationGSLT machine).termsAlone (contextTheory base turingPresentation) :=
  ContextMap.ofTerms (source := configurationGSLT machine)
    (target := contextTheory base turingPresentation) soups (unionTableTerm machine)
    (fun same => unionTableTerm_resp base machine same)

/-- **Under every evaluator of the premises the union hosts every Turing
machine on its configurations.**  The rewrites that do the work carry no
premise. -/
theorem turingMap_hosting (base : BasePremiseEvaluator) (machine : Machine) :
    (turingMap base machine).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := configurationGSLT machine)
    (target := contextTheory base turingPresentation) soups (unionTableTerm machine)
    (fun same => unionTableTerm_resp base machine same)).mpr ⟨?_, ?_, ?_⟩
  · intro (first : Configuration) (second : Configuration) related
    have settled : settle (unionTableTerm machine first).1 =
        settle (unionTableTerm machine second).1 :=
      probeWithTuring_quoteDropWithBags.settle_eq (equationEquiv_of_termSetoid related)
    unfold settle at settled
    rw [contract_of_soupTerm (unionTableTerm machine first),
      contract_of_soupTerm (unionTableTerm machine second)] at settled
    exact configuration_eq_of_normalForm_eq (machine := machine)
      (members := first.term :: description machine)
      (others := second.term :: description machine) (List.Perm.refl _) (List.Perm.refl _) settled
  · intro (first : Configuration) (next : Configuration) step
    obtain ⟨after, engineStep, afterHolds⟩ :=
      tableWith_forward (machine := machine) (members := first.term :: description machine)
        (List.Perm.refl _) step
    exact ⟨unionTableTerm machine first, ⟨soup after, tableWith_unionSorted afterHolds⟩,
      Relation.EqvGen.refl _,
      Step.transport_of_premiseFree (fun _ member => List.mem_append_right language.rewrites member)
        (fun rule member => (universalTheory_plain rule member).1) engineStep,
      union_bag_equiv base afterHolds (List.Perm.refl _) rfl rfl⟩
  · intro (first : Configuration) next step
    obtain ⟨redex, contractum, toRedex, fired, toNext⟩ := step
    have settled : settle (unionTableTerm machine first).1 = settle redex.1 :=
      probeWithTuring_quoteDropWithBags.settle_eq (equationEquiv_of_termSetoid toRedex)
    unfold settle at settled
    rw [contract_of_soupTerm (unionTableTerm machine first), contract_of_soupTerm redex] at settled
    obtain ⟨redexPattern, redexSorted⟩ := redex
    change normalForm none (soup (first.term :: description machine)) =
      normalForm none redexPattern at settled
    change Step base probeWithTuring redexPattern contractum.1 at fired
    obtain ⟨rule, member, fuel, initial, final, matched, premises, applied⟩ :=
      exists_rule_of_step fired
    rcases List.mem_append.mp member with inProbe | inUniversal
    · exfalso
      have isApply : ∃ label arguments, redexPattern = .apply label arguments := by
        change rule ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
          evaluationDemandRewrite, needRewrite, needReturnRewrite, reflectedDemandRewrite]
          at inProbe
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inProbe
        rcases inProbe with rfl | rfl | rfl | rfl | rfl | rfl <;>
          · obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
            exact ⟨_, arguments, shape⟩
      obtain ⟨label, arguments, rfl⟩ := isApply
      rw [soup, normalForm_bag, normalForm_apply] at settled
      simp [normalizeBag] at settled
    · have isBag : ∃ elements tail, redexPattern = .collection .hashBag elements tail := by
        have known := inUniversal
        simp only [universalTheory, List.mem_cons, List.not_mem_nil, or_false] at known
        rcases known with rfl | rfl | rfl | rfl <;>
          · have relation := matchPattern_iff_matchRel.mp matched
            cases relation with
            | collection notVector bagRelation => exact ⟨_, _, rfl⟩
      obtain ⟨elements, tail, rfl⟩ := isBag
      obtain ⟨others, redexShape, othersHold⟩ :=
        tableWith_of_normalForm_eq (machine := machine) (configuration := first)
          (members := first.term :: description machine) (List.Perm.refl _) settled
      have engineStep := universal_step_of_rule inUniversal matched premises applied
      rw [redexShape] at engineStep
      obtain ⟨nextPattern, afterMembers, machineStep, contractumShape, afterHold⟩ :=
        tableWith_backward othersHold engineStep
      obtain ⟨entry, inTable, applies, rfl⟩ := step_term_iff.mp machineStep
      refine ⟨first.after entry, machineStep, ?_⟩
      exact (termSetoid base probeWithTuring soups).iseqv.trans
        ((termSetoid base probeWithTuring soups).iseqv.symm toNext)
        (union_bag_equiv base afterHold (List.Perm.refl _) contractumShape rfl)

/-- **The sentence, at the level of the sources' contexts**: under every
evaluator the union hosts every machine. -/
theorem turingPresentation_hostsEvery_machineTheory (base : BasePremiseEvaluator) :
    HostsEvery (contextTheory base turingPresentation) MachineTheory := by
  rintro source ⟨machine, rfl⟩
  exact ⟨turingMap base machine, turingMap_hosting base machine⟩

/-- **The sentence for the route by own rewrites**: under every evaluator of
its premises, the union of the probe with the universal Turing theory is a
host of the Turing machines, on terms. -/
theorem turingPresentation_hostOf_machineTheory (base : BasePremiseEvaluator) :
    HostOf (contextTheory base turingPresentation) MachineTheory .terms .hosting :=
  HostOf.terms (hostOf_contexts_hosting_iff.mpr (turingPresentation_hostsEvery_machineTheory base))

/-- **One step of the machine is one step of the union**: a run of `count`
steps of a machine is a reduction of `count` steps of the union, under every
evaluator. -/
theorem turing_steps (base : BasePremiseEvaluator) (machine : Machine) {count : Nat}
    {first final : Configuration}
    (steps : (configurationGSLT machine).termsAlone.Steps (interface := PUnit.unit) count first
      final) :
    (contextTheory base turingPresentation).Steps count (unionTableTerm machine first)
      (unionTableTerm machine final) :=
  (turingMap base machine).steps_of_preserves (turingMap_hosting base machine).preserves steps

/-! ## Reductions of every length, under every evaluator -/

/-- The machine that moves right for ever on the blank tape. -/
def rightMover : Machine := ⟨[⟨0, 0, 0, .right, 0⟩]⟩

/-- Its configuration after `count` steps from the blank tape. -/
def movedRight (count : Nat) : Configuration :=
  { state := 0, left := List.replicate count 0, scanned := 0, right := [] }

theorem rightMover_step (count : Nat) :
    (configurationGSLT rightMover).rewrites (movedRight count) (movedRight (count + 1)) :=
  step_term_term_iff.mpr ⟨⟨0, 0, 0, .right, 0⟩, List.mem_singleton.mpr rfl, ⟨rfl, rfl⟩, rfl⟩

theorem rightMover_steps (count : Nat) :
    ∀ start : Nat, (configurationGSLT rightMover).termsAlone.Steps (interface := PUnit.unit) count
      (movedRight start) (movedRight (start + count)) := by
  induction count with
  | zero => exact fun start => .zero _
  | succ count ih =>
      intro start
      have rest := ih (start + 1)
      rw [Nat.add_right_comm] at rest
      exact .succ (rightMover_step start) rest

/-- **Under every evaluator the union has reductions of every length.** -/
theorem turing_steps_every_length (base : BasePremiseEvaluator) (count : Nat) :
    (contextTheory base turingPresentation).Steps count (unionTableTerm rightMover (movedRight 0))
      (unionTableTerm rightMover (movedRight count)) := by
  have steps := turing_steps base rightMover (rightMover_steps count 0)
  rwa [Nat.zero_add] at steps

/-- **Under every evaluator, the one that answers nothing included, the
union has no rank.**  The probe with the run constructor has one under that
evaluator. -/
theorem turingPresentation_not_rank (base : BasePremiseEvaluator) :
    IsEmpty (contextTheory base turingPresentation).Rank := by
  refine ⟨fun ranked => ?_⟩
  have bounded := ranked.steps_le
    (turing_steps_every_length base (ranked.rank (unionTableTerm rightMover (movedRight 0)) + 1))
  omega

/-! ## The map is not exhausting -/

/-- A row of the right mover alone, as a term of the union. -/
def loneRowTerm : Contexts.Term probeWithTuring soups :=
  ⟨rowTerm ⟨0, 0, 0, .right, 0⟩, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: a row outside every bag is a term of the union and the
image of no configuration, so the map is not exhausting. -/
theorem turingMap_not_exhausting (base : BasePremiseEvaluator) (machine : Machine) :
    ¬ (turingMap base machine).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit) loneRowTerm
  have settled : settle loneRowTerm.1 = settle (unionTableTerm machine preimage).1 :=
    probeWithTuring_quoteDropWithBags.settle_eq (equationEquiv_of_termSetoid related)
  unfold settle at settled
  rw [contract_of_soupTerm loneRowTerm, contract_of_soupTerm (unionTableTerm machine preimage)]
    at settled
  change normalForm none (rowTerm ⟨0, 0, 0, .right, 0⟩) =
    normalForm none (soup (preimage.term :: description machine)) at settled
  rw [soup, normalForm_bag, rowTerm, row, normalForm_apply] at settled
  simp [normalizeBag] at settled

#print axioms probeWithTuring_validate
#print axioms QuoteDropWithBags.settle_eq
#print axioms probeWithTuring_machineSorts_apart
#print axioms contract_of_soupTerm
#print axioms turingMap_hosting
#print axioms turingPresentation_hostsEvery_machineTheory
#print axioms turingPresentation_hostOf_machineTheory
#print axioms turing_steps
#print axioms turing_steps_every_length
#print axioms turingPresentation_not_rank
#print axioms turingMap_not_exhausting

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
