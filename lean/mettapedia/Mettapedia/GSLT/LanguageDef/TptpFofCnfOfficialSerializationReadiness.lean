import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationSemantics
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofElaboration

/-!
# Structural readiness for official TPTP CNF serialization

Official serialization is partial for principled reasons: numeric and
distinct-object terms are nullary, defined predicates are non-nullary, and
generated identities must have entries in a finite lexical plan.  This module
states those obligations over the semantic first-order objects and proves that
the independent serializer succeeds whenever they hold.

The predicates are not a second syntax checker.  They expose exactly the
conditions used by the official serializer, so a preceding official-AST
elaboration theorem can discharge them once and later transformations need
only preserve them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationReadiness

open Mettapedia.OSLF.MeTTaIL.Syntax
open TptpFofCnfOfficialSerializationPlan

abbrev LexicalPlan := TptpFofCnfOfficialSerializationPlan.Plan
abbrev Term := TptpFofDefinitionalNamingSemantics.Term
abbrev Reference := TptpFofDefinitionalNamingSemantics.Reference

/-! ## Official-source shape -/

/-- The shape restriction already enforced by the official term decoder,
stated on its named semantic result. -/
def NamedTermOriginalReady : TptpFofBinderResolution.NamedTerm -> Prop
  | .variable _ => True
  | .function head arguments =>
      (match head.kind with
        | .integer | .rational | .real | .distinctObject => arguments = []
        | .plain | .defined | .system => True) /\
      forall argument, argument ∈ arguments -> NamedTermOriginalReady argument

def NamedTermsOriginalReady (arguments : List TptpFofBinderResolution.NamedTerm) :
    Prop :=
  forall argument, argument ∈ arguments -> NamedTermOriginalReady argument

private structure TermDecoderReadiness (source : Pattern) : Prop where
  term : forall target, TptpOfficialFofElaboration.decodeTerm? source =
    some target -> NamedTermOriginalReady target
  arguments : forall target,
    TptpOfficialFofElaboration.decodeArguments? source = some target ->
      NamedTermsOriginalReady target
  functionTerm : forall target,
    TptpOfficialFofElaboration.decodeFunctionTerm? source = some target ->
      NamedTermOriginalReady target
  plainTerm : forall target,
    TptpOfficialFofElaboration.decodePlainTerm? source = some target ->
      NamedTermOriginalReady target
  definedTerm : forall target,
    TptpOfficialFofElaboration.decodeDefinedTerm? source = some target ->
      NamedTermOriginalReady target
  definedPlainTerm : forall target,
    TptpOfficialFofElaboration.decodeDefinedPlainTerm? source = some target ->
      NamedTermOriginalReady target
  systemTerm : forall target,
    TptpOfficialFofElaboration.decodeSystemTerm? source = some target ->
      NamedTermOriginalReady target

private theorem termDecoderReadinessStep (source : Pattern)
    (smaller : forall child, sizeOf child < sizeOf source ->
      TermDecoderReadiness child) : TermDecoderReadiness source := by
  refine {
    term := ?_
    arguments := ?_
    functionTerm := ?_
    plainTerm := ?_
    definedTerm := ?_
    definedPlainTerm := ?_
    systemTerm := ?_ }
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeTerm? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).functionTerm _ decoded
        · rcases Option.map_eq_some_iff.mp decoded with ⟨name, _, rfl⟩
          simp [NamedTermOriginalReady]
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeTerm?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeArguments? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨result, resultDecoded, equality⟩
          simp at equality
          subst target
          intro argument membership
          simp only [List.mem_singleton] at membership
          subst argument
          exact (smaller _ (by simp_all)).term _ resultDecoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨result, resultDecoded, rest⟩
          rcases Option.bind_eq_some_iff.mp rest with
            ⟨results, resultsDecoded, equality⟩
          simp at equality
          subst target
          intro argument membership
          simp only [List.mem_cons] at membership
          cases membership with
          | inl equality =>
              subst argument
              exact (smaller _ (by simp_all; omega)).term _ resultDecoded
          | inr membership =>
              exact (smaller _ (by simp_all)).arguments _
                resultsDecoded
                argument membership
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeArguments?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeFunctionTerm? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).plainTerm _ decoded
        · exact (smaller _ (by simp_all)).definedTerm _ decoded
        · exact (smaller _ (by simp_all)).systemTerm _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeFunctionTerm?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodePlainTerm? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, equality⟩
          simp at equality
          subst target
          simp [NamedTermOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, rest⟩
          rcases Option.bind_eq_some_iff.mp rest with
            ⟨results, resultsDecoded, equality⟩
          simp at equality
          subst target
          simpa [NamedTermOriginalReady, NamedTermsOriginalReady] using
            (smaller _ (by simp_all)).arguments _ resultsDecoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodePlainTerm?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeDefinedTerm? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨head, _, equality⟩
          simp at equality
          subst target
          cases head with
          | mk kind lexeme => cases kind <;> simp [NamedTermOriginalReady]
        · have equality := Option.some.inj decoded
          subst target
          simp [NamedTermOriginalReady]
        · exact (smaller _ (by simp_all; omega)).definedPlainTerm _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeDefinedTerm?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeDefinedPlainTerm? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, equality⟩
          simp at equality
          subst target
          simp [NamedTermOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, rest⟩
          rcases Option.bind_eq_some_iff.mp rest with
            ⟨results, resultsDecoded, equality⟩
          simp at equality
          subst target
          simpa [NamedTermOriginalReady, NamedTermsOriginalReady] using
            (smaller _ (by simp_all)).arguments _ resultsDecoded
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeDefinedPlainTerm?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeSystemTerm? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, equality⟩
          simp at equality
          subst target
          simp [NamedTermOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, rest⟩
          rcases Option.bind_eq_some_iff.mp rest with
            ⟨results, resultsDecoded, equality⟩
          simp at equality
          subst target
          simpa [NamedTermOriginalReady, NamedTermsOriginalReady] using
            (smaller _ (by simp_all)).arguments _ resultsDecoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeSystemTerm?] at decoded

private theorem termDecoderReadiness (source : Pattern) :
    TermDecoderReadiness source := by
  refine WellFounded.induction (measure sizeOf).wf source ?_
  intro current inductionHypothesis
  apply termDecoderReadinessStep current
  intro child smaller
  exact inductionHypothesis child smaller

theorem decodeTerm?_originalReady (source : Pattern)
    (target : TptpFofBinderResolution.NamedTerm)
    (decoded : TptpOfficialFofElaboration.decodeTerm? source = some target) :
    NamedTermOriginalReady target :=
  (termDecoderReadiness source).term target decoded

theorem decodeArguments?_originalReady (source : Pattern)
    (target : List TptpFofBinderResolution.NamedTerm)
    (decoded : TptpOfficialFofElaboration.decodeArguments? source = some target) :
    NamedTermsOriginalReady target :=
  (termDecoderReadiness source).arguments target decoded

/-- The analogous source-shape obligation on named formulas.  In particular,
defined predicates are non-nullary; `$true` and `$false` elaborate to the
dedicated truth constructors rather than zero-argument predicates. -/
def NamedFormulaOriginalReady : TptpFofBinderResolution.NamedFormula -> Prop
  | .verum | .falsum => True
  | .predicate head arguments =>
      (match head.kind with
        | .defined => arguments ≠ []
        | .plain | .system => True) /\
      NamedTermsOriginalReady arguments
  | .equal left right =>
      NamedTermOriginalReady left /\ NamedTermOriginalReady right
  | .not body => NamedFormulaOriginalReady body
  | .and left right | .or left right | .iff left right
  | .implies left right | .reverseImplies left right | .xor left right
  | .nor left right | .nand left right =>
      NamedFormulaOriginalReady left /\ NamedFormulaOriginalReady right
  | .all _ body | .ex _ body => NamedFormulaOriginalReady body

def NamedFormulasOriginalReady
    (formulas : List TptpFofBinderResolution.NamedFormula) : Prop :=
  forall formula, formula ∈ formulas -> NamedFormulaOriginalReady formula

private def namedConjunction :
    List TptpFofBinderResolution.NamedFormula ->
      TptpFofBinderResolution.NamedFormula
  | [] => .verum
  | formula :: rest =>
      rest.foldl TptpFofBinderResolution.NamedFormula.and formula

private def namedDisjunction :
    List TptpFofBinderResolution.NamedFormula ->
      TptpFofBinderResolution.NamedFormula
  | [] => .falsum
  | formula :: rest =>
      rest.foldl TptpFofBinderResolution.NamedFormula.or formula

private theorem namedFormulaConjunctionReady
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (ready : NamedFormulasOriginalReady formulas) :
    NamedFormulaOriginalReady (namedConjunction formulas) := by
  cases formulas with
  | nil => trivial
  | cons formula formulas =>
      simp only [namedConjunction]
      have headReady := ready formula (by simp)
      induction formulas generalizing formula with
      | nil => exact headReady
      | cons next rest inductionHypothesis =>
          simp only [List.foldl_cons]
          have nextReady := ready next (by simp)
          have combinedReady : NamedFormulaOriginalReady (.and formula next) :=
            ⟨headReady, nextReady⟩
          apply inductionHypothesis (.and formula next)
          · intro candidate membership
            simp only [List.mem_cons] at membership
            cases membership with
            | inl equality => simpa [equality] using combinedReady
            | inr membership => exact ready candidate (by simp [membership])
          · exact combinedReady

private theorem namedFormulaDisjunctionReady
    (formulas : List TptpFofBinderResolution.NamedFormula)
    (ready : NamedFormulasOriginalReady formulas) :
    NamedFormulaOriginalReady (namedDisjunction formulas) := by
  cases formulas with
  | nil => trivial
  | cons formula formulas =>
      simp only [namedDisjunction]
      have headReady := ready formula (by simp)
      induction formulas generalizing formula with
      | nil => exact headReady
      | cons next rest inductionHypothesis =>
          simp only [List.foldl_cons]
          have nextReady := ready next (by simp)
          have combinedReady : NamedFormulaOriginalReady (.or formula next) :=
            ⟨headReady, nextReady⟩
          apply inductionHypothesis (.or formula next)
          · intro candidate membership
            simp only [List.mem_cons] at membership
            cases membership with
            | inl equality => simpa [equality] using combinedReady
            | inr membership => exact ready candidate (by simp [membership])
          · exact combinedReady

private structure FormulaDecoderReadiness (source : Pattern) : Prop where
  formula : forall target, TptpOfficialFofElaboration.decodeFormula? source =
    some target -> NamedFormulaOriginalReady target
  logicFormula : forall target,
    TptpOfficialFofElaboration.decodeLogicFormula? source = some target ->
      NamedFormulaOriginalReady target
  binaryFormula : forall target,
    TptpOfficialFofElaboration.decodeBinaryFormula? source = some target ->
      NamedFormulaOriginalReady target
  binaryNonassoc : forall target,
    TptpOfficialFofElaboration.decodeBinaryNonassoc? source = some target ->
      NamedFormulaOriginalReady target
  binaryAssoc : forall target,
    TptpOfficialFofElaboration.decodeBinaryAssoc? source = some target ->
      NamedFormulaOriginalReady target
  orFormula : forall target,
    TptpOfficialFofElaboration.decodeOrFormula? source = some target ->
      NamedFormulaOriginalReady target
  andFormula : forall target,
    TptpOfficialFofElaboration.decodeAndFormula? source = some target ->
      NamedFormulaOriginalReady target
  unaryFormula : forall target,
    TptpOfficialFofElaboration.decodeUnaryFormula? source = some target ->
      NamedFormulaOriginalReady target
  unitFormula : forall target,
    TptpOfficialFofElaboration.decodeUnitFormula? source = some target ->
      NamedFormulaOriginalReady target
  unitaryFormula : forall target,
    TptpOfficialFofElaboration.decodeUnitaryFormula? source = some target ->
      NamedFormulaOriginalReady target
  quantifiedFormula : forall target,
    TptpOfficialFofElaboration.decodeQuantifiedFormula? source = some target ->
      NamedFormulaOriginalReady target
  atomicFormula : forall target,
    TptpOfficialFofElaboration.decodeAtomicFormula? source = some target ->
      NamedFormulaOriginalReady target
  plainAtomicFormula : forall target,
    TptpOfficialFofElaboration.decodePlainAtomicFormula? source = some target ->
      NamedFormulaOriginalReady target
  definedAtomicFormula : forall target,
    TptpOfficialFofElaboration.decodeDefinedAtomicFormula? source = some target ->
      NamedFormulaOriginalReady target
  definedPlainFormula : forall target,
    TptpOfficialFofElaboration.decodeDefinedPlainFormula? source = some target ->
      NamedFormulaOriginalReady target
  definedInfixFormula : forall target,
    TptpOfficialFofElaboration.decodeDefinedInfixFormula? source = some target ->
      NamedFormulaOriginalReady target
  systemAtomicFormula : forall target,
    TptpOfficialFofElaboration.decodeSystemAtomicFormula? source = some target ->
      NamedFormulaOriginalReady target
  infixUnary : forall target,
    TptpOfficialFofElaboration.decodeInfixUnary? source = some target ->
      NamedFormulaOriginalReady target
  sequent : forall target,
    TptpOfficialFofElaboration.decodeSequent? source = some target ->
      NamedFormulaOriginalReady target
  formulaTuple : forall target,
    TptpOfficialFofElaboration.decodeFormulaTuple? source = some target ->
      NamedFormulasOriginalReady target
  formulaTupleList : forall target,
    TptpOfficialFofElaboration.decodeFormulaTupleList? source = some target ->
      NamedFormulasOriginalReady target
  commaFormulaList : forall target,
    TptpOfficialFofElaboration.decodeCommaFormulaList? source = some target ->
      NamedFormulasOriginalReady target

private theorem namedFormulaAllReady
    (binders : List String) (body : TptpFofBinderResolution.NamedFormula)
    (ready : NamedFormulaOriginalReady body) :
    NamedFormulaOriginalReady
      (binders.foldr TptpFofBinderResolution.NamedFormula.all body) := by
  induction binders with
  | nil => exact ready
  | cons binder binders inductionHypothesis =>
      exact inductionHypothesis

private theorem namedFormulaExReady
    (binders : List String) (body : TptpFofBinderResolution.NamedFormula)
    (ready : NamedFormulaOriginalReady body) :
    NamedFormulaOriginalReady
      (binders.foldr TptpFofBinderResolution.NamedFormula.ex body) := by
  induction binders with
  | nil => exact ready
  | cons binder binders inductionHypothesis =>
      exact inductionHypothesis

private theorem formulaDecoderReadinessStep (source : Pattern)
    (smaller : forall child, sizeOf child < sizeOf source ->
      FormulaDecoderReadiness child) : FormulaDecoderReadiness source := by
  refine {
    formula := ?_
    logicFormula := ?_
    binaryFormula := ?_
    binaryNonassoc := ?_
    binaryAssoc := ?_
    orFormula := ?_
    andFormula := ?_
    unaryFormula := ?_
    unitFormula := ?_
    unitaryFormula := ?_
    quantifiedFormula := ?_
    atomicFormula := ?_
    plainAtomicFormula := ?_
    definedAtomicFormula := ?_
    definedPlainFormula := ?_
    definedInfixFormula := ?_
    systemAtomicFormula := ?_
    infixUnary := ?_
    sequent := ?_
    formulaTuple := ?_
    formulaTupleList := ?_
    commaFormulaList := ?_ }
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).logicFormula _ decoded
        · exact (smaller _ (by simp_all)).sequent _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeLogicFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).binaryFormula _ decoded
        · exact (smaller _ (by simp_all)).unaryFormula _ decoded
        · exact (smaller _ (by simp_all)).unitaryFormula _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeLogicFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeBinaryFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).binaryNonassoc _ decoded
        · exact (smaller _ (by simp_all)).binaryAssoc _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeBinaryFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeBinaryNonassoc? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, result⟩
          have leftReady :=
            (smaller _ (by simp_all; omega)).unitFormula _ leftDecoded
          have rightReady :=
            (smaller _ (by simp_all)).unitFormula _ rightDecoded
          split at result <;> try simp at result
          all_goals
            subst target
            exact ⟨leftReady, rightReady⟩
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeBinaryNonassoc?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeBinaryAssoc? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).orFormula _ decoded
        · exact (smaller _ (by simp_all)).andFormula _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeBinaryAssoc?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeOrFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(smaller _ (by simp_all; omega)).unitFormula _ leftDecoded,
            (smaller _ (by simp_all)).unitFormula _ rightDecoded⟩
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(smaller _ (by simp_all; omega)).orFormula _ leftDecoded,
            (smaller _ (by simp_all)).unitFormula _ rightDecoded⟩
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeOrFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeAndFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(smaller _ (by simp_all; omega)).unitFormula _ leftDecoded,
            (smaller _ (by simp_all)).unitFormula _ rightDecoded⟩
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(smaller _ (by simp_all; omega)).andFormula _ leftDecoded,
            (smaller _ (by simp_all)).unitFormula _ rightDecoded⟩
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeAndFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeUnaryFormula? at decoded
        split at decoded
        · rcases Option.map_eq_some_iff.mp decoded with
            ⟨body, bodyDecoded, equality⟩
          subst target
          exact (smaller _ (by simp_all)).unitFormula body bodyDecoded
        · exact (smaller _ (by simp_all)).infixUnary _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeUnaryFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeUnitFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).unitaryFormula _ decoded
        · exact (smaller _ (by simp_all)).unaryFormula _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeUnitFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeUnitaryFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).quantifiedFormula _ decoded
        · exact (smaller _ (by simp_all)).atomicFormula _ decoded
        · exact (smaller _ (by simp_all)).logicFormula _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeUnitaryFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeQuantifiedFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨binders, bindersDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨body, bodyDecoded, result⟩
          have bodyReady :=
            (smaller _ (by simp_all)).unitFormula _ bodyDecoded
          split at result
          · have equality := Option.some.inj result
            subst target
            exact namedFormulaAllReady binders body bodyReady
          · have equality := Option.some.inj result
            subst target
            exact namedFormulaExReady binders body bodyReady
          · simp at result
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeQuantifiedFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeAtomicFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).plainAtomicFormula _ decoded
        · exact (smaller _ (by simp_all)).definedAtomicFormula _ decoded
        · exact (smaller _ (by simp_all)).systemAtomicFormula _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeAtomicFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodePlainAtomicFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, equality⟩
          simp at equality
          subst target
          simp [NamedFormulaOriginalReady, NamedTermsOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨terms, termsDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨trivial, (termDecoderReadiness _).arguments _ termsDecoded⟩
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodePlainAtomicFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeDefinedAtomicFormula? at decoded
        split at decoded
        · exact (smaller _ (by simp_all)).definedPlainFormula _ decoded
        · exact (smaller _ (by simp_all)).definedInfixFormula _ decoded
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeDefinedAtomicFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeDefinedPlainFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨term, termDecoded, result⟩
          have termReady :=
            (termDecoderReadiness _).definedPlainTerm _ termDecoded
          split at result
          · have equality := Option.some.inj result
            subst target
            trivial
          · have equality := Option.some.inj result
            subst target
            trivial
          · have equality := Option.some.inj result
            subst target
            simp only [NamedTermOriginalReady] at termReady
            refine ⟨by simp, ?_⟩
            intro candidate membership
            simp only [List.mem_cons] at membership
            cases membership with
            | inl equality =>
                exact termReady.2 candidate (by simp [equality])
            | inr membership =>
                exact termReady.2 candidate (by simp [membership])
          · simp at result
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeDefinedPlainFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeDefinedInfixFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(termDecoderReadiness _).term _ leftDecoded,
            (termDecoderReadiness _).term _ rightDecoded⟩
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeDefinedInfixFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeSystemAtomicFormula? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, equality⟩
          simp at equality
          subst target
          simp [NamedFormulaOriginalReady, NamedTermsOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨name, _, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨terms, termsDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨trivial, (termDecoderReadiness _).arguments _ termsDecoded⟩
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeSystemAtomicFormula?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeInfixUnary? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftResult, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightResult, rightDecoded, equality⟩
          simp at equality
          subst target
          exact ⟨(termDecoderReadiness _).term _ leftDecoded,
            (termDecoderReadiness _).term _ rightDecoded⟩
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeInfixUnary?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeSequent? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨leftFormulas, leftDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨rightFormulas, rightDecoded, equality⟩
          simp at equality
          subst target
          constructor
          · change NamedFormulaOriginalReady (namedConjunction leftFormulas)
            exact namedFormulaConjunctionReady leftFormulas
              ((smaller _ (by simp_all; omega)).formulaTuple _ leftDecoded)
          · change NamedFormulaOriginalReady (namedDisjunction rightFormulas)
            exact namedFormulaDisjunctionReady rightFormulas
              ((smaller _ (by simp_all)).formulaTuple _ rightDecoded)
        · exact (smaller _ (by simp_all)).sequent _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeSequent?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeFormulaTuple? at decoded
        split at decoded
        · have equality := Option.some.inj decoded
          subst target
          simp [NamedFormulasOriginalReady]
        · exact (smaller _ (by simp_all)).formulaTupleList _ decoded
        · simp at decoded
    | _ => simp [TptpOfficialFofElaboration.decodeFormulaTuple?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeFormulaTupleList? at decoded
        split at decoded
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨formula, formulaDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨formulas, formulasDecoded, equality⟩
          simp at equality
          subst target
          intro candidate membership
          simp only [List.mem_cons] at membership
          cases membership with
          | inl equality =>
              subst candidate
              exact (smaller _ (by simp_all; omega)).logicFormula _ formulaDecoded
          | inr membership =>
              exact (smaller _ (by simp_all)).commaFormulaList _
                formulasDecoded candidate membership
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeFormulaTupleList?] at decoded
  · intro target decoded
    cases source with
    | apply label arguments =>
        unfold TptpOfficialFofElaboration.decodeCommaFormulaList? at decoded
        split at decoded
        · have equality := Option.some.inj decoded
          subst target
          simp [NamedFormulasOriginalReady]
        · rcases Option.bind_eq_some_iff.mp decoded with
            ⟨formula, formulaDecoded, remaining⟩
          rcases Option.bind_eq_some_iff.mp remaining with
            ⟨formulas, formulasDecoded, equality⟩
          simp at equality
          subst target
          intro candidate membership
          simp only [List.mem_cons] at membership
          cases membership with
          | inl equality =>
              subst candidate
              exact (smaller _ (by simp_all; omega)).logicFormula _ formulaDecoded
          | inr membership =>
              exact (smaller _ (by simp_all)).commaFormulaList _
                formulasDecoded candidate membership
        · simp at decoded
    | _ =>
        simp [TptpOfficialFofElaboration.decodeCommaFormulaList?] at decoded

private theorem formulaDecoderReadiness (source : Pattern) :
    FormulaDecoderReadiness source := by
  refine WellFounded.induction (measure sizeOf).wf source ?_
  intro current inductionHypothesis
  apply formulaDecoderReadinessStep current
  intro child smaller
  exact inductionHypothesis child smaller

theorem decodeFormula?_originalReady (source : Pattern)
    (target : TptpFofBinderResolution.NamedFormula)
    (decoded : TptpOfficialFofElaboration.decodeFormula? source = some target) :
    NamedFormulaOriginalReady target :=
  (formulaDecoderReadiness source).formula target decoded

/-- Exact lookup coverage needed by terms and references.  Clause-name
coverage is kept separate because it belongs to allocated batch entries. -/
structure Coverage (plan : LexicalPlan) (variableDepth skolemBound
    definitionBound : Nat) : Prop where
  variableLookup : ∀ index : Fin variableDepth,
    ∃ target, plan.variableNames.lookup?
      (TptpResolvedFofLanguageDef.encodeNatIndex index.val) = some target
  skolemLookup : ∀ identity : Nat, identity < skolemBound ->
    ∃ target, plan.skolemFunctors.lookup?
      (TptpResolvedFofLanguageDef.encodeNatIndex identity) = some target
  definitionLookup : ∀ identity : Nat, identity < definitionBound ->
    ∃ target, plan.definitionFunctors.lookup?
      (TptpResolvedFofLanguageDef.encodeNatIndex identity) = some target

def OriginalFunctionReady {arity : Nat}
    (function : TptpFofNormalizationSemantics.FunctionSymbol arity) : Prop :=
  match function.kind with
  | .integer | .rational | .real | .distinctObject => arity = 0
  | .plain | .defined | .system => True

def OriginalPredicateReady {arity : Nat}
    (predicate : TptpFofNormalizationSemantics.PredicateSymbol arity) : Prop :=
  match predicate.kind with
  | .defined => 0 < arity
  | .plain | .system => True

def TermReady {depth : Nat} (skolemBound : Nat) : Term depth -> Prop
  | .bvar _ => True
  | .fvar impossible => nomatch impossible
  | .func (.original function) arguments =>
      OriginalFunctionReady function /\
        ∀ index, TermReady skolemBound (arguments index)
  | .func (.generated identity) arguments =>
      identity < skolemBound /\
        ∀ index, TermReady skolemBound (arguments index)

def ReferenceReady {depth : Nat} (skolemBound definitionBound : Nat) :
    Reference depth -> Prop
  | .verum | .falsum => True
  | .positive (.original (.predicate predicate)) arguments
  | .negative (.original (.predicate predicate)) arguments =>
      OriginalPredicateReady predicate /\
        ∀ index, TermReady skolemBound (arguments index)
  | .positive (.original .equality) arguments
  | .negative (.original .equality) arguments =>
      ∀ index, TermReady skolemBound (arguments index)
  | .positive (.defined identity) arguments
  | .negative (.defined identity) arguments =>
      identity < definitionBound /\
        ∀ index, TermReady skolemBound (arguments index)

def ClauseReady {depth : Nat} (skolemBound definitionBound : Nat)
    (clause : TptpFofDefinitionalCnfSemantics.Clause depth) : Prop :=
  ∀ reference, reference ∈ clause ->
    ReferenceReady skolemBound definitionBound reference

def SourceTermReady {depth : Nat} (skolemBound : Nat) :
    TptpFofDefinitionalNamingSemantics.Source.Term depth -> Prop
  | .bvar _ => True
  | .fvar impossible => nomatch impossible
  | .func (.original function) arguments =>
      OriginalFunctionReady function /\
        ∀ index, SourceTermReady skolemBound (arguments index)
  | .func (.generated identity) arguments =>
      identity < skolemBound /\
        ∀ index, SourceTermReady skolemBound (arguments index)

def SourceTermOriginalReady {depth : Nat} :
    TptpFofDefinitionalNamingSemantics.Source.Term depth -> Prop
  | .bvar _ => True
  | .fvar impossible => nomatch impossible
  | .func (.original function) arguments =>
      OriginalFunctionReady function /\
        ∀ index, SourceTermOriginalReady (arguments index)
  | .func (.generated _) arguments =>
      ∀ index, SourceTermOriginalReady (arguments index)

def FormulaOriginalReady {depth : Nat} :
    TptpFofDefinitionalNamingSemantics.Source.Formula depth -> Prop
  | .verum | .falsum => True
  | .rel relation arguments | .nrel relation arguments =>
      (match relation with
        | .predicate predicate => OriginalPredicateReady predicate
        | .equality => True) /\
      ∀ index, SourceTermOriginalReady (arguments index)
  | .and left right | .or left right =>
      FormulaOriginalReady left /\ FormulaOriginalReady right
  | .all body | .ex body => FormulaOriginalReady body

def FormulaReady {depth : Nat} (skolemBound : Nat) :
    TptpFofDefinitionalNamingSemantics.Source.Formula depth -> Prop
  | .verum | .falsum => True
  | .rel relation arguments | .nrel relation arguments =>
      (match relation with
        | .predicate predicate => OriginalPredicateReady predicate
        | .equality => True) /\
      ∀ index, SourceTermReady skolemBound (arguments index)
  | .and left right | .or left right =>
      FormulaReady skolemBound left /\ FormulaReady skolemBound right
  | .all body | .ex body => FormulaReady skolemBound body

theorem sourceTermReady_of_original_generated {depth bound : Nat}
    (term : TptpFofDefinitionalNamingSemantics.Source.Term depth)
    (original : SourceTermOriginalReady term)
    (generated : TptpFofSkolemizationSemantics.TermGeneratedBelow bound term) :
    SourceTermReady bound term := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      cases function with
      | original sourceFunction =>
          exact ⟨original.1, fun index =>
            inductionHypothesis index (original.2 index) (generated index)⟩
      | generated identity =>
          exact ⟨generated.1, fun index =>
            inductionHypothesis index (original index) (generated.2 index)⟩

theorem formulaReady_of_original_generated {depth bound : Nat}
    (formula : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (original : FormulaOriginalReady formula)
    (generated :
      TptpFofSkolemizationSemantics.FormulaGeneratedBelow bound formula) :
    FormulaReady bound formula := by
  induction formula with
  | verum | falsum => trivial
  | rel relation arguments | nrel relation arguments =>
      exact ⟨original.1, fun index =>
        sourceTermReady_of_original_generated (arguments index)
          (original.2 index) (generated index)⟩
  | and left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis original.1 generated.1,
        rightHypothesis original.2 generated.2⟩
  | or left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis original.1 generated.1,
        rightHypothesis original.2 generated.2⟩
  | all body inductionHypothesis =>
      exact inductionHypothesis original generated
  | ex body inductionHypothesis =>
      exact inductionHypothesis original generated

def DefinitionReady {depth : Nat} (skolemBound definitionBound : Nat)
    (definition : TptpFofDefinitionalNamingSemantics.Definition depth) : Prop :=
  definition.id < definitionBound /\
    ReferenceReady skolemBound definitionBound definition.left /\
    ReferenceReady skolemBound definitionBound definition.right

def OutputReady {depth : Nat} (skolemBound : Nat)
    (output : TptpFofDefinitionalNamingSemantics.Output depth) : Prop :=
  ReferenceReady skolemBound output.next output.root /\
    ∀ definition, definition ∈ output.definitions ->
      DefinitionReady skolemBound output.next definition

theorem TermReady.mono {depth first second : Nat} (included : first ≤ second)
    {term : Term depth} (ready : TermReady first term) :
    TermReady second term := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      cases function with
      | original sourceFunction =>
          exact ⟨ready.1, fun index =>
            inductionHypothesis index (ready.2 index)⟩
      | generated identity =>
          exact ⟨Nat.lt_of_lt_of_le ready.1 included, fun index =>
            inductionHypothesis index (ready.2 index)⟩

theorem ReferenceReady.monoDefinition {depth skolemBound first second : Nat}
    (included : first ≤ second) {reference : Reference depth}
    (ready : ReferenceReady skolemBound first reference) :
    ReferenceReady skolemBound second reference := by
  cases reference with
  | verum | falsum => trivial
  | positive relation arguments | negative relation arguments =>
      cases relation with
      | original sourceRelation =>
          cases sourceRelation <;> exact ready
      | defined identity =>
          exact ⟨Nat.lt_of_lt_of_le ready.1 included, ready.2⟩

theorem translateTerm_ready {depth skolemBound : Nat}
    (term : TptpFofDefinitionalNamingSemantics.Source.Term depth)
    (ready : SourceTermReady skolemBound term) :
    TermReady skolemBound
      (TptpFofDefinitionalNamingSemantics.translateTerm term) := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      cases function with
      | original sourceFunction =>
          exact ⟨ready.1, fun index =>
            inductionHypothesis index (ready.2 index)⟩
      | generated identity =>
          exact ⟨ready.1, fun index =>
            inductionHypothesis index (ready.2 index)⟩

theorem sourceReference_ready {depth skolemBound definitionBound : Nat}
    (formula : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (ready : FormulaReady skolemBound formula) :
    ReferenceReady skolemBound definitionBound
      (TptpFofDefinitionalNamingSemantics.sourceReference formula) := by
  cases formula with
  | verum | falsum | and | or | all | ex => trivial
  | rel relation arguments | nrel relation arguments =>
      cases relation with
      | predicate predicate =>
          exact ⟨ready.1, fun index =>
            translateTerm_ready (arguments index) (ready.2 index)⟩
      | equality =>
          exact fun index =>
            translateTerm_ready (arguments index) (ready.2 index)

theorem definedReference_ready (depth identity skolemBound definitionBound : Nat)
    (bounded : identity < definitionBound) :
    ReferenceReady skolemBound definitionBound
      (TptpFofDefinitionalNamingSemantics.definedReference depth identity) := by
  exact ⟨bounded, fun _ => trivial⟩

theorem negate_ready {depth skolemBound definitionBound : Nat}
    (reference : Reference depth)
    (ready : ReferenceReady skolemBound definitionBound reference) :
    ReferenceReady skolemBound definitionBound
      (TptpFofDefinitionalCnfSemantics.negate reference) := by
  cases reference with
  | verum | falsum => trivial
  | positive relation arguments | negative relation arguments =>
      cases relation with
      | original sourceRelation => cases sourceRelation <;> exact ready
      | defined => exact ready

theorem OutputReady.monoDefinition {depth skolemBound first second : Nat}
    (included : first ≤ second)
    {output : TptpFofDefinitionalNamingSemantics.Output depth}
    (ready : OutputReady skolemBound output)
    (nextExact : output.next = first) :
    ReferenceReady skolemBound second output.root /\
      ∀ definition, definition ∈ output.definitions ->
        DefinitionReady skolemBound second definition := by
  subst first
  refine ⟨ready.1.monoDefinition included, ?_⟩
  intro definition membership
  have definitionReady := ready.2 definition membership
  exact ⟨Nat.lt_of_lt_of_le definitionReady.1 included,
    definitionReady.2.1.monoDefinition included,
    definitionReady.2.2.monoDefinition included⟩

theorem nameFrom_outputReady {depth skolemBound : Nat}
    (source : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (quantifierFree :
      TptpFofDefinitionalNamingSemantics.QuantifierFree source)
    (frontier : Nat) (sourceReady : FormulaReady skolemBound source) :
    OutputReady skolemBound
      (TptpFofDefinitionalNamingSemantics.nameFrom source quantifierFree
        frontier) := by
  induction source generalizing frontier with
  | verum =>
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      exact ⟨trivial, fun definition membership => by
        simp [TptpFofDefinitionalNamingSemantics.leafOutput] at membership⟩
  | falsum =>
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      exact ⟨trivial, fun definition membership => by
        simp [TptpFofDefinitionalNamingSemantics.leafOutput] at membership⟩
  | rel relation arguments =>
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      refine ⟨sourceReference_ready (.rel relation arguments) sourceReady,
        ?_⟩
      intro definition membership
      simp [TptpFofDefinitionalNamingSemantics.leafOutput] at membership
  | nrel relation arguments =>
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      refine ⟨sourceReference_ready (.nrel relation arguments) sourceReady,
        ?_⟩
      intro definition membership
      simp [TptpFofDefinitionalNamingSemantics.leafOutput] at membership
  | @and branchDepth left right leftHypothesis rightHypothesis =>
      have sourceReady' : FormulaReady skolemBound left /\
          FormulaReady skolemBound right := sourceReady
      let leftOutput :=
        TptpFofDefinitionalNamingSemantics.nameFrom left quantifierFree.1
          frontier
      let rightOutput :=
        TptpFofDefinitionalNamingSemantics.nameFrom right quantifierFree.2
          leftOutput.next
      have leftReady : OutputReady skolemBound leftOutput :=
        leftHypothesis quantifierFree.1 frontier sourceReady'.1
      have rightReady : OutputReady skolemBound rightOutput :=
        rightHypothesis quantifierFree.2 leftOutput.next sourceReady'.2
      have rightNext : rightOutput.next = leftOutput.next +
          TptpFofDefinitionalNamingSemantics.connectiveCount right := by
        dsimp [rightOutput]
        exact TptpFofDefinitionalNamingSemantics.nameFrom_next_exact
          right quantifierFree.2 leftOutput.next
      have leftToRight : leftOutput.next ≤ rightOutput.next := by
        rw [rightNext]
        omega
      have leftAtFinal := leftReady.monoDefinition
        (Nat.le_trans leftToRight (Nat.le_add_right rightOutput.next 1)) rfl
      have rightAtFinal := rightReady.monoDefinition
        (Nat.le_add_right rightOutput.next 1) rfl
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      change OutputReady skolemBound {
        root := TptpFofDefinitionalNamingSemantics.definedReference branchDepth
          rightOutput.next
        next := rightOutput.next + 1
        definitions := leftOutput.definitions ++ rightOutput.definitions ++ [({
          id := rightOutput.next
          source := .and left right
          connective := .and
          left := leftOutput.root
          right := rightOutput.root } :
            TptpFofDefinitionalNamingSemantics.Definition branchDepth)]
        introduced := leftOutput.introduced ++ rightOutput.introduced ++ [{
          id := rightOutput.next
          arity := branchDepth }] }
      refine ⟨definedReference_ready branchDepth rightOutput.next skolemBound
        (rightOutput.next + 1) (by omega), ?_⟩
      intro definition membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with (leftMembership | rightMembership) | rfl
      · exact leftAtFinal.2 definition leftMembership
      · exact rightAtFinal.2 definition rightMembership
      · refine ⟨?_, leftAtFinal.1, rightAtFinal.1⟩
        change rightOutput.next < rightOutput.next + 1
        omega
  | @or branchDepth left right leftHypothesis rightHypothesis =>
      have sourceReady' : FormulaReady skolemBound left /\
          FormulaReady skolemBound right := sourceReady
      let leftOutput :=
        TptpFofDefinitionalNamingSemantics.nameFrom left quantifierFree.1
          frontier
      let rightOutput :=
        TptpFofDefinitionalNamingSemantics.nameFrom right quantifierFree.2
          leftOutput.next
      have leftReady : OutputReady skolemBound leftOutput :=
        leftHypothesis quantifierFree.1 frontier sourceReady'.1
      have rightReady : OutputReady skolemBound rightOutput :=
        rightHypothesis quantifierFree.2 leftOutput.next sourceReady'.2
      have rightNext : rightOutput.next = leftOutput.next +
          TptpFofDefinitionalNamingSemantics.connectiveCount right := by
        dsimp [rightOutput]
        exact TptpFofDefinitionalNamingSemantics.nameFrom_next_exact
          right quantifierFree.2 leftOutput.next
      have leftToRight : leftOutput.next ≤ rightOutput.next := by
        rw [rightNext]
        omega
      have leftAtFinal := leftReady.monoDefinition
        (Nat.le_trans leftToRight (Nat.le_add_right rightOutput.next 1)) rfl
      have rightAtFinal := rightReady.monoDefinition
        (Nat.le_add_right rightOutput.next 1) rfl
      simp only [TptpFofDefinitionalNamingSemantics.nameFrom]
      change OutputReady skolemBound {
        root := TptpFofDefinitionalNamingSemantics.definedReference branchDepth
          rightOutput.next
        next := rightOutput.next + 1
        definitions := leftOutput.definitions ++ rightOutput.definitions ++ [({
          id := rightOutput.next
          source := .or left right
          connective := .or
          left := leftOutput.root
          right := rightOutput.root } :
            TptpFofDefinitionalNamingSemantics.Definition branchDepth)]
        introduced := leftOutput.introduced ++ rightOutput.introduced ++ [{
          id := rightOutput.next
          arity := branchDepth }] }
      refine ⟨definedReference_ready branchDepth rightOutput.next skolemBound
        (rightOutput.next + 1) (by omega), ?_⟩
      intro definition membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with (leftMembership | rightMembership) | rfl
      · exact leftAtFinal.2 definition leftMembership
      · exact rightAtFinal.2 definition rightMembership
      · refine ⟨?_, leftAtFinal.1, rightAtFinal.1⟩
        change rightOutput.next < rightOutput.next + 1
        omega
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem clausesForDefinition_ready {depth skolemBound definitionBound : Nat}
    (definition : TptpFofDefinitionalNamingSemantics.Definition depth)
    (ready : DefinitionReady skolemBound definitionBound definition) :
    ∀ clause,
      clause ∈ TptpFofDefinitionalCnfSemantics.clausesForDefinition
        definition ->
      ClauseReady skolemBound definitionBound clause := by
  cases definition with
  | mk identity source connective left right =>
    have headReady := definedReference_ready depth identity skolemBound
      definitionBound ready.1
    have negativeHeadReady := negate_ready _ headReady
    have negativeLeftReady := negate_ready left ready.2.1
    have negativeRightReady := negate_ready right ready.2.2
    cases connective with
    | and =>
      intro clause membership
      simp [TptpFofDefinitionalCnfSemantics.clausesForDefinition] at membership
      rcases membership with rfl | rfl | rfl
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl
        · exact negativeHeadReady
        · exact ready.2.1
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl
        · exact negativeHeadReady
        · exact ready.2.2
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl | rfl
        · exact headReady
        · exact negativeLeftReady
        · exact negativeRightReady
    | or =>
      intro clause membership
      simp [TptpFofDefinitionalCnfSemantics.clausesForDefinition] at membership
      rcases membership with rfl | rfl | rfl
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl | rfl
        · exact negativeHeadReady
        · exact ready.2.1
        · exact ready.2.2
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl
        · exact headReady
        · exact negativeLeftReady
      · intro reference referenceMembership
        simp at referenceMembership
        rcases referenceMembership with rfl | rfl
        · exact headReady
        · exact negativeRightReady

theorem clausesForDefinitions_ready {depth skolemBound definitionBound : Nat}
    (definitions :
      List (TptpFofDefinitionalNamingSemantics.Definition depth))
    (ready : ∀ definition, definition ∈ definitions ->
      DefinitionReady skolemBound definitionBound definition) :
    ∀ clause,
      clause ∈
        TptpFofDefinitionalCnfSemantics.clausesForDefinitions definitions ->
      ClauseReady skolemBound definitionBound clause := by
  induction definitions with
  | nil =>
      intro clause membership
      simp [TptpFofDefinitionalCnfSemantics.clausesForDefinitions] at membership
  | cons definition definitions inductionHypothesis =>
      intro clause membership
      simp only [TptpFofDefinitionalCnfSemantics.clausesForDefinitions,
        List.mem_append] at membership
      rcases membership with headMembership | tailMembership
      · exact clausesForDefinition_ready definition
          (ready definition (by simp)) clause headMembership
      · exact inductionHypothesis
          (fun candidate candidateMembership =>
            ready candidate (by simp [candidateMembership]))
          clause tailMembership

theorem clausesForOutput_ready {depth skolemBound : Nat}
    (output : TptpFofDefinitionalNamingSemantics.Output depth)
    (ready : OutputReady skolemBound output) :
    ∀ clause,
      clause ∈ TptpFofDefinitionalCnfSemantics.clausesForOutput output ->
      ClauseReady skolemBound output.next clause := by
  intro clause membership
  simp only [TptpFofDefinitionalCnfSemantics.clausesForOutput,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with definitionMembership | rfl
  · exact clausesForDefinitions_ready output.definitions ready.2 clause
      definitionMembership
  · intro reference referenceMembership
    simp only [List.mem_singleton] at referenceMembership
    simpa [referenceMembership] using ready.1

theorem nameFrom_clausesReady {depth skolemBound : Nat}
    (source : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (quantifierFree :
      TptpFofDefinitionalNamingSemantics.QuantifierFree source)
    (frontier : Nat) (sourceReady : FormulaReady skolemBound source) :
    ∀ clause, clause ∈
        TptpFofDefinitionalCnfSemantics.clausesForOutput
          (TptpFofDefinitionalNamingSemantics.nameFrom source quantifierFree
            frontier) ->
      ClauseReady skolemBound
        (TptpFofDefinitionalNamingSemantics.nameFrom source quantifierFree
          frontier).next clause :=
  clausesForOutput_ready _
    (nameFrom_outputReady source quantifierFree frontier sourceReady)

private theorem serializePatternVector_exists (plan : LexicalPlan) :
    ∀ {arity : Nat} (patterns : Fin arity -> Pattern),
      (∀ index, ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
          (patterns index) = some rendered) ->
      ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeTerms? plan
          (TptpFofSkolemLanguageDef.encodeTermPatterns
            (List.ofFn patterns)) = some rendered
  | 0, _, _ => ⟨[], rfl⟩
  | arity + 1, patterns, children => by
      obtain ⟨head, headExact⟩ := children 0
      obtain ⟨tail, tailExact⟩ :=
        serializePatternVector_exists plan (fun index => patterns index.succ)
          (fun index => children index.succ)
      refine ⟨head :: tail, ?_⟩
      simp [List.ofFn_succ, TptpFofSkolemLanguageDef.encodeTermPatterns,
        TptpFofSkolemLanguageDef.termsCons, TptpFofSkolemLanguageDef.a,
        TptpFofCnfOfficialSerializationSemantics.serializeTerms?, headExact,
        tailExact]

private theorem serializePatternVector_exists_length (plan : LexicalPlan) :
    ∀ {arity : Nat} (patterns : Fin arity -> Pattern),
      (∀ index, ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
          (patterns index) = some rendered) ->
      ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeTerms? plan
            (TptpFofSkolemLanguageDef.encodeTermPatterns
              (List.ofFn patterns)) = some rendered /\
          rendered.length = arity
  | 0, _, _ => ⟨[], rfl, rfl⟩
  | arity + 1, patterns, children => by
      obtain ⟨head, headExact⟩ := children 0
      obtain ⟨tail, tailExact, tailLength⟩ :=
        serializePatternVector_exists_length plan
          (fun index => patterns index.succ)
          (fun index => children index.succ)
      refine ⟨head :: tail, ?_, ?_⟩
      · simp [List.ofFn_succ, TptpFofSkolemLanguageDef.encodeTermPatterns,
          TptpFofSkolemLanguageDef.termsCons, TptpFofSkolemLanguageDef.a,
          TptpFofCnfOfficialSerializationSemantics.serializeTerms?, headExact,
          tailExact]
      · simp [tailLength]

private theorem arguments_exists_of_ne_nil : ∀ (terms : List Pattern),
    terms ≠ [] -> ∃ rendered,
      TptpFofCnfOfficialSerializationSemantics.arguments terms = some rendered
  | [], nonempty => (nonempty rfl).elim
  | [head], _ =>
      ⟨TptpFofCnfOfficialSerializationSemantics.a
        "tptp92-ast:fof-arguments:alt-1" [head], rfl⟩
  | head :: second :: tail, _ => by
      obtain ⟨renderedTail, tailExact⟩ :=
        arguments_exists_of_ne_nil (second :: tail) (by simp)
      refine ⟨TptpFofCnfOfficialSerializationSemantics.a
        "tptp92-ast:fof-arguments:alt-2" [head, renderedTail], ?_⟩
      simp [TptpFofCnfOfficialSerializationSemantics.arguments, tailExact]

private theorem encodeNamedTerm_generated {depth arity identity : Nat}
    (arguments : Fin arity -> Term depth) :
    TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
        (.func (.generated identity) arguments) =
      TptpFofSkolemLanguageDef.termGenerated
        (TptpResolvedFofLanguageDef.encodeNatIndex identity)
        (TptpFofSkolemLanguageDef.encodeTermPatterns
          (List.ofFn fun index =>
            TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
              (arguments index))) := by
  rfl

private theorem encodeNamedTerm_original {depth arity : Nat}
    (function : TptpFofNormalizationSemantics.FunctionSymbol arity)
    (arguments : Fin arity -> Term depth) :
    TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
        (.func (.original function) arguments) =
      TptpFofSkolemLanguageDef.termOriginal
        (TptpFofSymbolLanguageDef.encodeFunctionHead
          ⟨function.kind, function.name⟩)
        (TptpFofSkolemLanguageDef.encodeTermPatterns
          (List.ofFn fun index =>
            TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
              (arguments index))) := by
  rfl

theorem serializeTerm_exists (plan : LexicalPlan)
    {depth skolemBound definitionBound : Nat}
    (coverage : Coverage plan depth skolemBound definitionBound)
    (term : Term depth) (ready : TermReady skolemBound term) :
    ∃ rendered,
      TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm term) =
          some rendered := by
  induction term with
  | bvar index =>
      obtain ⟨target, lookup⟩ := coverage.variableLookup index
      refine ⟨TptpFofCnfOfficialSerializationSemantics.a
        "tptp92-ast:fof-term:alt-2" [target], ?_⟩
      simp only [TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm,
        TptpResolvedFofLanguageDef.encodeIndex,
        TptpFofSkolemLanguageDef.termVariable,
        TptpFofSkolemLanguageDef.a,
        TptpFofCnfOfficialSerializationSemantics.serializeTerm?]
      rw [lookup]
      rfl
  | fvar impossible => exact nomatch impossible
  | @func arity function arguments inductionHypothesis =>
      change TptpFofSkolemizationSemantics.FunctionSymbol arity at function
      cases function with
      | original sourceFunction =>
          have ready' : OriginalFunctionReady sourceFunction /\
              ∀ index, TermReady skolemBound (arguments index) := by
            simpa [TermReady] using ready
          have children : ∀ index, ∃ rendered,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                  (arguments index)) = some rendered :=
            fun index => inductionHypothesis index (ready'.2 index)
          obtain ⟨renderedArguments, argumentsExact⟩ :=
            serializePatternVector_exists plan
              (fun index => TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                (arguments index)) children
          cases kind : sourceFunction.kind
          case plain =>
            refine ⟨TptpFofCnfOfficialSerializationSemantics.plainTerm
              (TptpFofCnfOfficialSerializationSemantics.functorPlain
                (.apply sourceFunction.name [])) renderedArguments, ?_⟩
            rw [encodeNamedTerm_original]
            simp only [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?]
            rw [argumentsExact]
            simp [TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind]
          case defined =>
            refine ⟨TptpFofCnfOfficialSerializationSemantics.definedTerm
              (TptpFofCnfOfficialSerializationSemantics.definedFunctor
                (.apply sourceFunction.name [])) renderedArguments, ?_⟩
            rw [encodeNamedTerm_original]
            simp only [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?]
            rw [argumentsExact]
            simp [TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind]
          case system =>
            refine ⟨TptpFofCnfOfficialSerializationSemantics.systemTerm
              (TptpFofCnfOfficialSerializationSemantics.systemFunctor
                (.apply sourceFunction.name [])) renderedArguments, ?_⟩
            rw [encodeNamedTerm_original]
            simp only [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?]
            rw [argumentsExact]
            simp [TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind]
          case integer =>
            simp only [OriginalFunctionReady, kind] at ready'
            have arityZero : arity = 0 := ready'.1
            subst arity
            refine ⟨TptpFofCnfOfficialSerializationSemantics.numericTerm
              "tptp92-ast:number:alt-1" "tptp92-ast:token:integer"
              (.apply sourceFunction.name []), ?_⟩
            rw [encodeNamedTerm_original]
            simp [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?,
              TptpFofCnfOfficialSerializationSemantics.serializeTerms?,
              TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind,
              List.ofFn_zero,
              TptpFofSkolemLanguageDef.encodeTermPatterns,
              TptpFofSkolemLanguageDef.termsNil]
          case rational =>
            simp only [OriginalFunctionReady, kind] at ready'
            have arityZero : arity = 0 := ready'.1
            subst arity
            refine ⟨TptpFofCnfOfficialSerializationSemantics.numericTerm
              "tptp92-ast:number:alt-2" "tptp92-ast:token:rational"
              (.apply sourceFunction.name []), ?_⟩
            rw [encodeNamedTerm_original]
            simp [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?,
              TptpFofCnfOfficialSerializationSemantics.serializeTerms?,
              TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind,
              List.ofFn_zero,
              TptpFofSkolemLanguageDef.encodeTermPatterns,
              TptpFofSkolemLanguageDef.termsNil]
          case real =>
            simp only [OriginalFunctionReady, kind] at ready'
            have arityZero : arity = 0 := ready'.1
            subst arity
            refine ⟨TptpFofCnfOfficialSerializationSemantics.numericTerm
              "tptp92-ast:number:alt-3" "tptp92-ast:token:real"
              (.apply sourceFunction.name []), ?_⟩
            rw [encodeNamedTerm_original]
            simp [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?,
              TptpFofCnfOfficialSerializationSemantics.serializeTerms?,
              TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind,
              List.ofFn_zero,
              TptpFofSkolemLanguageDef.encodeTermPatterns,
              TptpFofSkolemLanguageDef.termsNil]
          case distinctObject =>
            simp only [OriginalFunctionReady, kind] at ready'
            have arityZero : arity = 0 := ready'.1
            subst arity
            refine ⟨TptpFofCnfOfficialSerializationSemantics.distinctObjectTerm
              (.apply sourceFunction.name []), ?_⟩
            rw [encodeNamedTerm_original]
            simp [
              TptpFofSkolemLanguageDef.termOriginal,
              TptpFofSkolemLanguageDef.a,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm?,
              TptpFofCnfOfficialSerializationSemantics.serializeTerms?,
              TptpFofSymbolLanguageDef.encodeFunctionHead,
              TptpFofSymbolLanguageDef.a, kind,
              List.ofFn_zero,
              TptpFofSkolemLanguageDef.encodeTermPatterns,
              TptpFofSkolemLanguageDef.termsNil]
      | generated identity =>
          have ready' : identity < skolemBound /\
              ∀ index, TermReady skolemBound (arguments index) := by
            simpa [TermReady] using ready
          have children : ∀ index, ∃ rendered,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                  (arguments index)) = some rendered :=
            fun index => inductionHypothesis index (ready'.2 index)
          obtain ⟨renderedArguments, argumentsExact⟩ :=
            serializePatternVector_exists plan
              (fun index => TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                (arguments index)) children
          obtain ⟨target, lookup⟩ :=
            coverage.skolemLookup identity ready'.1
          refine ⟨TptpFofCnfOfficialSerializationSemantics.plainTerm target
            renderedArguments, ?_⟩
          rw [encodeNamedTerm_generated]
          simp only [
            TptpFofSkolemLanguageDef.termGenerated,
            TptpFofSkolemLanguageDef.a,
            TptpFofCnfOfficialSerializationSemantics.serializeTerm?]
          rw [lookup, argumentsExact]
          rfl

theorem serializeReference_exists (plan : LexicalPlan)
    {depth skolemBound definitionBound : Nat}
    (coverage : Coverage plan depth skolemBound definitionBound)
    (reference : Reference depth)
    (ready : ReferenceReady skolemBound definitionBound reference) :
    ∃ rendered,
      TptpFofCnfOfficialSerializationSemantics.serializeReference? plan
        (TptpFofDefinitionalCnfLanguageDef.encodeReference reference) =
          some rendered := by
  cases reference with
  | verum =>
      exact ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
        (TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula "$true"),
        rfl⟩
  | falsum =>
      exact ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
        (TptpFofCnfOfficialSerializationSemantics.truthAtomicFormula "$false"),
        rfl⟩
  | @positive arity relation arguments =>
      cases relation with
      | original sourceRelation =>
          cases sourceRelation with
          | predicate predicate =>
              have ready' : OriginalPredicateReady predicate /\
                  ∀ index, TermReady skolemBound (arguments index) := by
                simpa [ReferenceReady] using ready
              have children : ∀ index, ∃ rendered,
                  TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                    (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                      (arguments index)) = some rendered :=
                fun index => serializeTerm_exists plan coverage
                  (arguments index) (ready'.2 index)
              obtain ⟨renderedArguments, argumentsExact, argumentsLength⟩ :=
                serializePatternVector_exists_length plan
                  (fun index =>
                    TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                      (arguments index)) children
              cases kind : predicate.kind
              case plain =>
                refine ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
                  (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
                    (TptpFofCnfOfficialSerializationSemantics.functorPlain
                      (.apply predicate.name [])) renderedArguments), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
              case system =>
                refine ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
                  (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
                    (TptpFofCnfOfficialSerializationSemantics.systemFunctor
                      (.apply predicate.name [])) renderedArguments), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
              case defined =>
                have arityPositive : 0 < arity := by
                  simpa [OriginalPredicateReady, kind] using ready'.1
                have renderedNonempty : renderedArguments ≠ [] := by
                  intro empty
                  have : renderedArguments.length = 0 := by simp [empty]
                  omega
                obtain ⟨renderedList, renderedListExact⟩ :=
                  arguments_exists_of_ne_nil renderedArguments renderedNonempty
                refine ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
                  (TptpFofCnfOfficialSerializationSemantics.a
                    "tptp92-ast:fof-atomic-formula:alt-2" [
                      TptpFofCnfOfficialSerializationSemantics.a
                        "tptp92-ast:fof-defined-atomic-formula:alt-1" [
                          TptpFofCnfOfficialSerializationSemantics.a
                            "tptp92-ast:fof-defined-plain-formula:alt-1" [
                              TptpFofCnfOfficialSerializationSemantics.a
                                "tptp92-ast:fof-defined-plain-term:alt-2" [
                                  TptpFofCnfOfficialSerializationSemantics.definedFunctor
                                    (.apply predicate.name []),
                                  renderedList]]]]), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?,
                  TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
                  renderedListExact]
          | equality =>
              have ready' : ∀ index, TermReady skolemBound (arguments index) := by
                simpa [ReferenceReady] using ready
              obtain ⟨left, leftExact⟩ :=
                serializeTerm_exists plan coverage (arguments 0) (ready' 0)
              obtain ⟨right, rightExact⟩ :=
                serializeTerm_exists plan coverage (arguments 1) (ready' 1)
              refine ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
                (TptpFofCnfOfficialSerializationSemantics.equalityAtomicFormula
                  left right), ?_⟩
              simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                TptpFofDefinitionalCnfLanguageDef.refEqual,
                TptpFofDefinitionalCnfLanguageDef.a,
                TptpFofCnfOfficialSerializationSemantics.serializeReference?]
              rw [leftExact, rightExact]
              rfl
      | defined identity =>
          have ready' : identity < definitionBound /\
              ∀ index, TermReady skolemBound (arguments index) := by
            simpa [ReferenceReady] using ready
          obtain ⟨target, lookup⟩ :=
            coverage.definitionLookup identity ready'.1
          have children : ∀ index, ∃ rendered,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                  (arguments index)) = some rendered :=
            fun index => serializeTerm_exists plan coverage
              (arguments index) (ready'.2 index)
          obtain ⟨renderedArguments, argumentsExact⟩ :=
            serializePatternVector_exists plan
              (fun index => TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                (arguments index)) children
          refine ⟨TptpFofCnfOfficialSerializationSemantics.positiveLiteral
            (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
              target renderedArguments), ?_⟩
          simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
            TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
            TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
            TptpFofDefinitionalCnfLanguageDef.a,
            TptpFofCnfOfficialSerializationSemantics.serializeReference?]
          rw [lookup, argumentsExact]
          rfl
  | @negative arity relation arguments =>
      cases relation with
      | original sourceRelation =>
          cases sourceRelation with
          | predicate predicate =>
              have ready' : OriginalPredicateReady predicate /\
                  ∀ index, TermReady skolemBound (arguments index) := by
                simpa [ReferenceReady] using ready
              have children : ∀ index, ∃ rendered,
                  TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                    (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                      (arguments index)) = some rendered :=
                fun index => serializeTerm_exists plan coverage
                  (arguments index) (ready'.2 index)
              obtain ⟨renderedArguments, argumentsExact, argumentsLength⟩ :=
                serializePatternVector_exists_length plan
                  (fun index =>
                    TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                      (arguments index)) children
              cases kind : predicate.kind
              case plain =>
                refine ⟨TptpFofCnfOfficialSerializationSemantics.negativeLiteral
                  (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
                    (TptpFofCnfOfficialSerializationSemantics.functorPlain
                      (.apply predicate.name [])) renderedArguments), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
              case system =>
                refine ⟨TptpFofCnfOfficialSerializationSemantics.negativeLiteral
                  (TptpFofCnfOfficialSerializationSemantics.systemAtomicFormula
                    (TptpFofCnfOfficialSerializationSemantics.systemFunctor
                      (.apply predicate.name [])) renderedArguments), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?]
              case defined =>
                have arityPositive : 0 < arity := by
                  simpa [OriginalPredicateReady, kind] using ready'.1
                have renderedNonempty : renderedArguments ≠ [] := by
                  intro empty
                  have : renderedArguments.length = 0 := by simp [empty]
                  omega
                obtain ⟨renderedList, renderedListExact⟩ :=
                  arguments_exists_of_ne_nil renderedArguments renderedNonempty
                refine ⟨TptpFofCnfOfficialSerializationSemantics.negativeLiteral
                  (TptpFofCnfOfficialSerializationSemantics.a
                    "tptp92-ast:fof-atomic-formula:alt-2" [
                      TptpFofCnfOfficialSerializationSemantics.a
                        "tptp92-ast:fof-defined-atomic-formula:alt-1" [
                          TptpFofCnfOfficialSerializationSemantics.a
                            "tptp92-ast:fof-defined-plain-formula:alt-1" [
                              TptpFofCnfOfficialSerializationSemantics.a
                                "tptp92-ast:fof-defined-plain-term:alt-2" [
                                  TptpFofCnfOfficialSerializationSemantics.definedFunctor
                                    (.apply predicate.name []),
                                  renderedList]]]]), ?_⟩
                simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                  TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
                  TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
                  TptpFofDefinitionalCnfLanguageDef.a,
                  TptpFofCnfOfficialSerializationSemantics.serializeReference?]
                rw [argumentsExact]
                simp [TptpFofSymbolLanguageDef.encodePredicateHead,
                  TptpFofSymbolLanguageDef.a, kind,
                  TptpFofCnfOfficialSerializationSemantics.serializeOriginalAtomic?,
                  TptpFofCnfOfficialSerializationSemantics.definedAtomicFormula?,
                  renderedListExact]
          | equality =>
              have ready' : ∀ index, TermReady skolemBound (arguments index) := by
                simpa [ReferenceReady] using ready
              obtain ⟨left, leftExact⟩ :=
                serializeTerm_exists plan coverage (arguments 0) (ready' 0)
              obtain ⟨right, rightExact⟩ :=
                serializeTerm_exists plan coverage (arguments 1) (ready' 1)
              refine ⟨TptpFofCnfOfficialSerializationSemantics.inequalityLiteral
                left right, ?_⟩
              simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
                TptpFofDefinitionalCnfLanguageDef.refNotEqual,
                TptpFofDefinitionalCnfLanguageDef.a,
                TptpFofCnfOfficialSerializationSemantics.serializeReference?]
              rw [leftExact, rightExact]
              rfl
      | defined identity =>
          have ready' : identity < definitionBound /\
              ∀ index, TermReady skolemBound (arguments index) := by
            simpa [ReferenceReady] using ready
          obtain ⟨target, lookup⟩ :=
            coverage.definitionLookup identity ready'.1
          have children : ∀ index, ∃ rendered,
              TptpFofCnfOfficialSerializationSemantics.serializeTerm? plan
                (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                  (arguments index)) = some rendered :=
            fun index => serializeTerm_exists plan coverage
              (arguments index) (ready'.2 index)
          obtain ⟨renderedArguments, argumentsExact⟩ :=
            serializePatternVector_exists plan
              (fun index => TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm
                (arguments index)) children
          refine ⟨TptpFofCnfOfficialSerializationSemantics.negativeLiteral
            (TptpFofCnfOfficialSerializationSemantics.plainAtomicFormula
              target renderedArguments), ?_⟩
          simp only [TptpFofDefinitionalCnfLanguageDef.encodeReference,
            TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms,
            TptpFofDefinitionalCnfLanguageDef.refDefinedNegative,
            TptpFofDefinitionalCnfLanguageDef.a,
            TptpFofCnfOfficialSerializationSemantics.serializeReference?]
          rw [lookup, argumentsExact]
          rfl

private theorem serializeClauseLiterals_exists (plan : LexicalPlan)
    {depth skolemBound definitionBound : Nat}
    (coverage : Coverage plan depth skolemBound definitionBound) :
    ∀ (clause : TptpFofDefinitionalCnfSemantics.Clause depth),
      ClauseReady skolemBound definitionBound clause ->
      ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals? plan
          (TptpFofDefinitionalCnfLanguageDef.encodeClause clause) =
            some rendered
  | [], _ => ⟨[], rfl⟩
  | head :: tail, ready => by
      have headReady : ReferenceReady skolemBound definitionBound head :=
        ready head (by simp)
      have tailReady : ClauseReady skolemBound definitionBound tail := by
        intro reference membership
        exact ready reference (by simp [membership])
      obtain ⟨renderedHead, headExact⟩ :=
        serializeReference_exists plan coverage head headReady
      obtain ⟨renderedTail, tailExact⟩ :=
        serializeClauseLiterals_exists plan coverage tail tailReady
      refine ⟨renderedHead :: renderedTail, ?_⟩
      simp [TptpFofDefinitionalCnfLanguageDef.encodeClause,
        TptpFofDefinitionalCnfLanguageDef.clauseCons,
        TptpFofDefinitionalCnfLanguageDef.a,
        TptpFofCnfOfficialSerializationSemantics.serializeClauseLiterals?,
        headExact, tailExact]

theorem serializeClause_exists (plan : LexicalPlan)
    {depth skolemBound definitionBound : Nat}
    (coverage : Coverage plan depth skolemBound definitionBound)
    (clause : TptpFofDefinitionalCnfSemantics.Clause depth)
    (ready : ClauseReady skolemBound definitionBound clause) :
    ∃ rendered,
      TptpFofCnfOfficialSerializationSemantics.serializeClause? plan
        (TptpFofDefinitionalCnfLanguageDef.encodeClause clause) =
          some rendered := by
  obtain ⟨renderedLiterals, literalsExact⟩ :=
    serializeClauseLiterals_exists plan coverage clause ready
  refine ⟨TptpFofCnfOfficialSerializationSemantics.a
    "tptp92-ast:cnf-formula:alt-1" [
      TptpFofCnfOfficialSerializationSemantics.disjunction renderedLiterals],
    ?_⟩
  simp only [TptpFofCnfOfficialSerializationSemantics.serializeClause?]
  rw [literalsExact]
  rfl

#print axioms serializeTerm_exists
#print axioms serializeReference_exists
#print axioms serializeClause_exists

end Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationReadiness
