import Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission
import Mettapedia.GSLT.Parsing.PlainBnfTrieSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution

/-!
# Authored diagnostic append and validation finishing

The actual admission occurrences 5–6 and 61–65, and graph occurrences 90–91,
are translated into the existing contextual relation by their checked modes.
Finishing inspects constructors; it does not validate opaque supplied fields.
The ordered diagnostic observation retains repetitions and source payloads.
These selected source execution results do not qualify a native backend.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfValidationFinishSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfReferenceSourceAdmission (admissionSource graphSource)
open PlainBnfTrieSourceExecution (call result result_injective)
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? : String → Option (Nat × Nat)
  | "BNFAppendDiagnosticsV1" => some (2, 1)
  | "BNFStartAfterLookupV1" => some (2, 2)
  | "BNFFinishValidationV1" => some (5, 1)
  | "BNFFinishGraphAnalysisV1" => some (7, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom head :: arguments) => do
      let (inputs, outputs) ← mode? head
      if arguments.length = inputs + outputs then
        some (.list (.atom head :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? (source : SExpr) : Option Premise := do
  let (input, output) ← splitCall? source
  some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def admissionRows : List Rewrite :=
  (admissionSource.rewrites.drop 5).take 2 ++ (admissionSource.rewrites.drop 61).take 5
def graphRows : List Rewrite := (graphSource.rewrites.drop 90).take 2
def rows : List Rewrite := admissionRows ++ graphRows
def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)
def language : LanguageDef :=
  { name := "PlainBnfAuthoredValidationFinish", types := [], terms := [], equations := [], rewrites := rules }

theorem translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl
theorem source_rule_count : language.rewrites.length = 9 := rfl
theorem admission_occurrences_exact :
    ((admissionSource.rewrites.zipIdx).drop 5).take 2 ++
      ((admissionSource.rewrites.zipIdx).drop 61).take 5 =
    ((admissionSource.rewrites.drop 5).take 2).zipIdx 5 ++
      ((admissionSource.rewrites.drop 61).take 5).zipIdx 61 := rfl
theorem graph_occurrences_exact : ((graphSource.rewrites.zipIdx).drop 90).take 2 = graphRows.zipIdx 90 := rfl
def relationHeads : List String :=
  ["BNFAppendDiagnosticsV1", "BNFStartAfterLookupV1", "BNFFinishValidationV1", "BNFFinishGraphAnalysisV1"]
theorem admission_exhaustive : admissionSource.rewrites.filter (fun row => match row.head with
    | .list (.atom head :: _) => relationHeads.contains head
    | _ => false) = admissionRows := rfl
theorem graph_exhaustive : graphSource.rewrites.filter (fun row => match row.head with
    | .list (.atom head :: _) => relationHeads.contains head
    | _ => false) = graphRows := rfl

/- Checked proof observations only. Executable rules are computed from rows. -/
private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }
private def observedRules : List RewriteRule := [
  observed "bnf-append-diagnostics-nil-v1"
    (metta_sexpr% petta "(BNFAppendDiagnosticsV1 BNFDiagnosticsNilV1 ?right)")
    (metta_sexpr% petta "(?right)"),
  observed "bnf-append-diagnostics-cons-v1"
    (metta_sexpr% petta "(BNFAppendDiagnosticsV1 (BNFDiagnosticsConsV1 ?head ?tail) ?right)")
    (metta_sexpr% petta "((BNFDiagnosticsConsV1 ?head ?after))")
    [metta_sexpr% petta "(BNFAppendDiagnosticsV1 ?tail ?right ?after)"],
  observed "bnf-start-found-v1"
    (metta_sexpr% petta "(BNFStartAfterLookupV1 ?name (BNFDefinitionFoundV1 ?expression ?span))")
    (metta_sexpr% petta "((BNFStartSomeV1 ?name ?span) BNFDiagnosticsNilV1)"),
  observed "bnf-start-missing-v1"
    (metta_sexpr% petta "(BNFStartAfterLookupV1 ?name BNFDefinitionMissingV1)")
    (metta_sexpr% petta "((BNFStartInvalidV1 ?name) (BNFDiagnosticsConsV1 (BNFUnknownStartV1 ?name) BNFDiagnosticsNilV1))"),
  observed "bnf-finish-no-definitions-v1"
    (metta_sexpr% petta "(BNFFinishValidationV1 ?documentSpan ?start BNFDefinitionsNilV1 ?lexicals ?diagnostics)")
    (metta_sexpr% petta "((BNFDeclarationValidationRefusedV1 (BNFDiagnosticsConsV1 (BNFNoDefinitionsV1 ?documentSpan) ?diagnostics)))"),
  observed "bnf-finish-accepted-v1"
    (metta_sexpr% petta "(BNFFinishValidationV1 ?documentSpan (BNFStartSomeV1 ?name ?span) (BNFDefinitionsConsV1 ?head ?tail) ?lexicals BNFDiagnosticsNilV1)")
    (metta_sexpr% petta "((BNFDeclarationValidationAcceptedV1 (BNFStartSomeV1 ?name ?span) (BNFDefinitionsConsV1 ?head ?tail) ?lexicals))"),
  observed "bnf-finish-refused-v1"
    (metta_sexpr% petta "(BNFFinishValidationV1 ?documentSpan ?start (BNFDefinitionsConsV1 ?definition ?definitions) ?lexicals (BNFDiagnosticsConsV1 ?head ?tail))")
    (metta_sexpr% petta "((BNFDeclarationValidationRefusedV1 (BNFDiagnosticsConsV1 ?head ?tail)))"),
  observed "bnf-finish-analysis-accepted-v1"
    (metta_sexpr% petta "(BNFFinishGraphAnalysisV1 ?start ?definitions ?lexicals ?reachable ?nullable ?productive BNFDiagnosticsNilV1)")
    (metta_sexpr% petta "((BNFSemanticValidationAcceptedV1 ?start ?definitions ?lexicals (BNFGrammarAnalysisV1 ?reachable ?nullable ?productive)))"),
  observed "bnf-finish-analysis-refused-v1"
    (metta_sexpr% petta "(BNFFinishGraphAnalysisV1 ?start ?definitions ?lexicals ?reachable ?nullable ?productive (BNFDiagnosticsConsV1 ?head ?tail))")
    (metta_sexpr% petta "((BNFSemanticValidationRefusedV1 (BNFDiagnosticsConsV1 ?head ?tail)))")]
private theorem rules_exact : language.rewrites = observedRules := rfl

theorem family_heads : language.rewrites.all (fun rule => headedBy relationHeads rule.left) = true := by
  simp [rules_exact, observedRules, observed, headedBy, relationHeads, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [rules_exact, observedRules, observed, premiseClosed, headedBy, relationHeads,
    lowerPremise?, splitCall?, mode?, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode]

def nil : SExpr := .atom "BNFDiagnosticsNilV1"
def cons (head tail : SExpr) : SExpr := .list [.atom "BNFDiagnosticsConsV1", head, tail]
def diagnostics (values : List SExpr) : SExpr := values.foldr cons nil
def prepend (values : List SExpr) (right : SExpr) : SExpr := values.foldr cons right
def appendCall (left right : SExpr) := call "BNFAppendDiagnosticsV1" [left, right]
def startCall (name lookup : SExpr) := call "BNFStartAfterLookupV1" [name, lookup]
def startSome (name span : SExpr) : SExpr := .list [.atom "BNFStartSomeV1", name, span]
def startInvalid (name : SExpr) : SExpr := .list [.atom "BNFStartInvalidV1", name]
def unknownStart (name : SExpr) : SExpr := .list [.atom "BNFUnknownStartV1", name]
def definitionsCons (head tail : SExpr) : SExpr := .list [.atom "BNFDefinitionsConsV1", head, tail]
def finishCall (documentSpan start definitions lexicals diagnostics : SExpr) :=
  call "BNFFinishValidationV1" [documentSpan, start, definitions, lexicals, diagnostics]
def accepted (start definitions lexicals : SExpr) : SExpr :=
  .list [.atom "BNFDeclarationValidationAcceptedV1", start, definitions, lexicals]
def refused (diagnostics : SExpr) : SExpr := .list [.atom "BNFDeclarationValidationRefusedV1", diagnostics]
def noDefinitions (span : SExpr) : SExpr := .list [.atom "BNFNoDefinitionsV1", span]
def graphCall (start definitions lexicals reachable nullable productive diagnostics : SExpr) :=
  call "BNFFinishGraphAnalysisV1" [start, definitions, lexicals, reachable, nullable, productive, diagnostics]
def graphAccepted (start definitions lexicals reachable nullable productive : SExpr) : SExpr :=
  .list [.atom "BNFSemanticValidationAcceptedV1", start, definitions, lexicals,
    .list [.atom "BNFGrammarAnalysisV1", reachable, nullable, productive]]
def graphRefused (diagnostics : SExpr) : SExpr := .list [.atom "BNFSemanticValidationRefusedV1", diagnostics]

theorem append_nil (base : BasePremiseEvaluator) (fuel : Nat) (right : SExpr) :
    rewriteAt base language (fuel + 1) (appendCall nil right) = [result right] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    appendCall, call, result, nil, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem append_cons (base : BasePremiseEvaluator) (fuel : Nat)
    (head tail right : SExpr) (answers : List SExpr)
    (recursive : rewriteAt base language fuel (appendCall tail right) = answers.map result) :
    rewriteAt base language (fuel + 1) (appendCall (cons head tail) right) =
      answers.map (fun answer => result (cons head answer)) := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, applyRuleUsing, appendCall, call, cons,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
    lowerPremise?, splitCall?, mode?, premiseStepUsing, applyBindings]
  simp only [appendCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

theorem append_answers (base : BasePremiseEvaluator) (fuel : Nat) (left : List SExpr) (right : SExpr) :
    rewriteAt base language fuel (appendCall (diagnostics left) right) =
      if left.length < fuel then [result (prepend left right)] else [] := by
  induction fuel generalizing left with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases left with
      | nil => simpa [diagnostics, prepend] using append_nil base fuel right
      | cons head tail =>
          by_cases enough : tail.length < fuel
          · have recursive := ih tail
            simp only [enough, ↓reduceIte] at recursive
            have next := append_cons base fuel head (diagnostics tail) right [prepend tail right]
              (by simpa using recursive)
            simpa [diagnostics, prepend, enough] using next
          · have recursive := ih tail
            simp only [enough, ↓reduceIte] at recursive
            have next := append_cons base fuel head (diagnostics tail) right [] (by simpa using recursive)
            simpa [diagnostics, enough] using next

theorem append_step_iff (base : BasePremiseEvaluator) (left : List SExpr) (right : SExpr) (target : Pattern) :
    Step base language (appendCall (diagnostics left) right) target ↔ target = result (prepend left right) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [append_answers] at member
    split at member
    · simpa using member
    · simp at member
  · intro same
    subst target
    exact ⟨left.length + 1, by simp [append_answers]⟩

theorem prepend_diagnostics (left right : List SExpr) :
    prepend left (diagnostics right) = diagnostics (left ++ right) := by
  simp [prepend, diagnostics, List.foldr_append]

theorem diagnostics_injective : Function.Injective diagnostics := by
  intro left right same
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons head tail => simp [diagnostics, cons, nil] at same
  | cons head tail ih => cases right with
    | nil => simp [diagnostics, cons, nil] at same
    | cons other rest =>
      simp only [diagnostics, List.foldr_cons, cons, SExpr.list.injEq, List.cons.injEq,
        and_true, true_and] at same
      exact congrArg₂ List.cons same.1 (ih same.2)

theorem append_decoded_step_iff (base : BasePremiseEvaluator) (left right output : List SExpr) :
    Step base language (appendCall (diagnostics left) (diagnostics right)) (result (diagnostics output)) ↔
      output = left ++ right := by
  rw [append_step_iff, prepend_diagnostics, result_injective.eq_iff, diagnostics_injective.eq_iff]

theorem append_nil_iff (base : BasePremiseEvaluator) (left right : List SExpr) :
    Step base language (appendCall (diagnostics left) (diagnostics right)) (result nil) ↔
      left = [] ∧ right = [] := by
  change Step base language (appendCall (diagnostics left) (diagnostics right)) (result (diagnostics [])) ↔ _
  rw [append_decoded_step_iff, eq_comm, List.append_eq_nil_iff]


private theorem fact_step_iff (base : BasePremiseEvaluator) (input output target : Pattern)
    (answers : ∀ fuel, rewriteAt base language (fuel + 1) input = [output]) :
    Step base language input target ↔ target = output := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => simp [rewriteAt] at member
    | succ fuel => simpa only [answers, List.mem_singleton] using member
  · intro same
    subst target
    exact ⟨1, by rw [answers]; simp⟩

theorem start_found_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (name expression span : SExpr) :
    rewriteAt base language (fuel + 1) (startCall name (.list [.atom "BNFDefinitionFoundV1", expression, span])) = [encode (.list [startSome name span, nil])] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, startCall, startSome, nil]

theorem start_found_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (name expression span : SExpr) :
    rewriteAt base language fuel (startCall name (.list [.atom "BNFDefinitionFoundV1", expression, span])) =
      if fuel = 0 then [] else [encode (.list [startSome name span, nil])] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using start_found_positive_depth base fuel name expression span

theorem start_found_step_iff (base : BasePremiseEvaluator)
    (name expression span : SExpr) (target : Pattern) :
    Step base language (startCall name (.list [.atom "BNFDefinitionFoundV1", expression, span])) target ↔ target = encode (.list [startSome name span, nil]) :=
  fact_step_iff base _ _ target (fun fuel => start_found_positive_depth base fuel name expression span)

theorem start_missing_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (name : SExpr) :
    rewriteAt base language (fuel + 1) (startCall name (.atom "BNFDefinitionMissingV1")) = [encode (.list [startInvalid name, cons (unknownStart name) nil])] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, startCall, startInvalid, cons, unknownStart, nil]

theorem start_missing_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (name : SExpr) :
    rewriteAt base language fuel (startCall name (.atom "BNFDefinitionMissingV1")) =
      if fuel = 0 then [] else [encode (.list [startInvalid name, cons (unknownStart name) nil])] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using start_missing_positive_depth base fuel name

theorem start_missing_step_iff (base : BasePremiseEvaluator)
    (name : SExpr) (target : Pattern) :
    Step base language (startCall name (.atom "BNFDefinitionMissingV1")) target ↔ target = encode (.list [startInvalid name, cons (unknownStart name) nil]) :=
  fact_step_iff base _ _ target (fun fuel => start_missing_positive_depth base fuel name)

theorem finish_empty_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan start lexicals ds : SExpr) :
    rewriteAt base language (fuel + 1) (finishCall documentSpan start (.atom "BNFDefinitionsNilV1") lexicals ds) = [result (refused (cons (noDefinitions documentSpan) ds))] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, finishCall, refused, cons, noDefinitions]

theorem finish_empty_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan start lexicals ds : SExpr) :
    rewriteAt base language fuel (finishCall documentSpan start (.atom "BNFDefinitionsNilV1") lexicals ds) =
      if fuel = 0 then [] else [result (refused (cons (noDefinitions documentSpan) ds))] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using finish_empty_positive_depth base fuel documentSpan start lexicals ds

theorem finish_empty_step_iff (base : BasePremiseEvaluator)
    (documentSpan start lexicals ds : SExpr) (target : Pattern) :
    Step base language (finishCall documentSpan start (.atom "BNFDefinitionsNilV1") lexicals ds) target ↔ target = result (refused (cons (noDefinitions documentSpan) ds)) :=
  fact_step_iff base _ _ target (fun fuel => finish_empty_positive_depth base fuel documentSpan start lexicals ds)

theorem finish_accepted_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan name span head tail lexicals : SExpr) :
    rewriteAt base language (fuel + 1) (finishCall documentSpan (startSome name span) (definitionsCons head tail) lexicals nil) = [result (accepted (startSome name span) (definitionsCons head tail) lexicals)] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, finishCall, startSome, definitionsCons, nil, accepted]

theorem finish_accepted_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan name span head tail lexicals : SExpr) :
    rewriteAt base language fuel (finishCall documentSpan (startSome name span) (definitionsCons head tail) lexicals nil) =
      if fuel = 0 then [] else [result (accepted (startSome name span) (definitionsCons head tail) lexicals)] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using finish_accepted_positive_depth base fuel documentSpan name span head tail lexicals

theorem finish_accepted_step_iff (base : BasePremiseEvaluator)
    (documentSpan name span head tail lexicals : SExpr) (target : Pattern) :
    Step base language (finishCall documentSpan (startSome name span) (definitionsCons head tail) lexicals nil) target ↔ target = result (accepted (startSome name span) (definitionsCons head tail) lexicals) :=
  fact_step_iff base _ _ target (fun fuel => finish_accepted_positive_depth base fuel documentSpan name span head tail lexicals)

theorem finish_refused_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan start head tail lexicals first rest : SExpr) :
    rewriteAt base language (fuel + 1) (finishCall documentSpan start (definitionsCons head tail) lexicals (cons first rest)) = [result (refused (cons first rest))] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, finishCall, definitionsCons, cons, refused]

theorem finish_refused_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan start head tail lexicals first rest : SExpr) :
    rewriteAt base language fuel (finishCall documentSpan start (definitionsCons head tail) lexicals (cons first rest)) =
      if fuel = 0 then [] else [result (refused (cons first rest))] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using finish_refused_positive_depth base fuel documentSpan start head tail lexicals first rest

theorem finish_refused_step_iff (base : BasePremiseEvaluator)
    (documentSpan start head tail lexicals first rest : SExpr) (target : Pattern) :
    Step base language (finishCall documentSpan start (definitionsCons head tail) lexicals (cons first rest)) target ↔ target = result (refused (cons first rest)) :=
  fact_step_iff base _ _ target (fun fuel => finish_refused_positive_depth base fuel documentSpan start head tail lexicals first rest)

theorem graph_accepted_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (start defs lexicals reachable nullable productive : SExpr) :
    rewriteAt base language (fuel + 1) (graphCall start defs lexicals reachable nullable productive nil) = [result (graphAccepted start defs lexicals reachable nullable productive)] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, graphCall, graphAccepted, nil]

theorem graph_accepted_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (start defs lexicals reachable nullable productive : SExpr) :
    rewriteAt base language fuel (graphCall start defs lexicals reachable nullable productive nil) =
      if fuel = 0 then [] else [result (graphAccepted start defs lexicals reachable nullable productive)] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using graph_accepted_positive_depth base fuel start defs lexicals reachable nullable productive

theorem graph_accepted_step_iff (base : BasePremiseEvaluator)
    (start defs lexicals reachable nullable productive : SExpr) (target : Pattern) :
    Step base language (graphCall start defs lexicals reachable nullable productive nil) target ↔ target = result (graphAccepted start defs lexicals reachable nullable productive) :=
  fact_step_iff base _ _ target (fun fuel => graph_accepted_positive_depth base fuel start defs lexicals reachable nullable productive)

theorem graph_refused_positive_depth (base : BasePremiseEvaluator) (fuel : Nat)
    (start defs lexicals reachable nullable productive first rest : SExpr) :
    rewriteAt base language (fuel + 1) (graphCall start defs lexicals reachable nullable productive (cons first rest)) = [result (graphRefused (cons first rest))] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings, graphCall, graphRefused, cons]

theorem graph_refused_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (start defs lexicals reachable nullable productive first rest : SExpr) :
    rewriteAt base language fuel (graphCall start defs lexicals reachable nullable productive (cons first rest)) =
      if fuel = 0 then [] else [result (graphRefused (cons first rest))] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa using graph_refused_positive_depth base fuel start defs lexicals reachable nullable productive first rest

theorem graph_refused_step_iff (base : BasePremiseEvaluator)
    (start defs lexicals reachable nullable productive first rest : SExpr) (target : Pattern) :
    Step base language (graphCall start defs lexicals reachable nullable productive (cons first rest)) target ↔ target = result (graphRefused (cons first rest)) :=
  fact_step_iff base _ _ target (fun fuel => graph_refused_positive_depth base fuel start defs lexicals reachable nullable productive first rest)

theorem invalid_start_without_diagnostics_answers (base : BasePremiseEvaluator) (fuel : Nat)
    (documentSpan name head tail lexicals : SExpr) :
    rewriteAt base language fuel
      (finishCall documentSpan (startInvalid name) (definitionsCons head tail) lexicals nil) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
      call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      finishCall, startInvalid, definitionsCons, nil]

theorem invalid_start_without_diagnostics_no_step (base : BasePremiseEvaluator)
    (documentSpan name head tail lexicals : SExpr) (target : Pattern) :
    ¬ Step base language
      (finishCall documentSpan (startInvalid name) (definitionsCons head tail) lexicals nil) target := by
  rw [← exists_mem_rewriteAt_iff_step]
  simp [invalid_start_without_diagnostics_answers]

theorem empty_refusal_preserves_diagnostics (base : BasePremiseEvaluator)
    (documentSpan start lexicals : SExpr) (ds : List SExpr) (target : Pattern) :
    Step base language (finishCall documentSpan start (.atom "BNFDefinitionsNilV1") lexicals (diagnostics ds)) target ↔
      target = result (refused (diagnostics (noDefinitions documentSpan :: ds))) := by
  simpa only [diagnostics, List.foldr_cons] using
    finish_empty_step_iff base documentSpan start lexicals (diagnostics ds) target

theorem finish_refused_diagnostics_step_iff (base : BasePremiseEvaluator)
    (documentSpan start head tail lexicals first : SExpr) (rest output : List SExpr) :
    Step base language
      (finishCall documentSpan start (definitionsCons head tail) lexicals (diagnostics (first :: rest)))
      (result (refused (diagnostics output))) ↔ output = first :: rest := by
  change Step base language
    (finishCall documentSpan start (definitionsCons head tail) lexicals (cons first (diagnostics rest)))
    (result (refused (diagnostics output))) ↔ _
  rw [finish_refused_step_iff, result_injective.eq_iff]
  simp only [refused, SExpr.list.injEq, List.cons.injEq, true_and, and_true]
  change diagnostics output = diagnostics (first :: rest) ↔ _
  exact diagnostics_injective.eq_iff

theorem graph_refused_diagnostics_step_iff (base : BasePremiseEvaluator)
    (start defs lexicals reachable nullable productive first : SExpr) (rest output : List SExpr) :
    Step base language
      (graphCall start defs lexicals reachable nullable productive (diagnostics (first :: rest)))
      (result (graphRefused (diagnostics output))) ↔ output = first :: rest := by
  change Step base language
    (graphCall start defs lexicals reachable nullable productive (cons first (diagnostics rest)))
    (result (graphRefused (diagnostics output))) ↔ _
  rw [graph_refused_step_iff, result_injective.eq_iff]
  simp only [graphRefused, SExpr.list.injEq, List.cons.injEq, true_and, and_true]
  change diagnostics output = diagnostics (first :: rest) ↔ _
  exact diagnostics_injective.eq_iff

theorem append_five_nil_iff (base : BasePremiseEvaluator) (a b c d e : List SExpr) :
    Step base language (appendCall (diagnostics (a ++ b)) (diagnostics (c ++ d ++ e))) (result nil) ↔
      a = [] ∧ b = [] ∧ c = [] ∧ d = [] ∧ e = [] := by
  simp [append_nil_iff, List.append_eq_nil_iff, and_assoc]

theorem repeated_diagnostics_survive (base : BasePremiseEvaluator) (entry : SExpr) :
    Step base language (appendCall (diagnostics [entry]) (diagnostics [entry]))
      (result (diagnostics [entry, entry])) ∧
    ¬ Step base language (appendCall (diagnostics [entry]) (diagnostics [entry]))
      (result (diagnostics [entry])) := by
  simp [append_decoded_step_iff]

theorem refusal_order_cannot_change (base : BasePremiseEvaluator)
    (documentSpan start head tail lexicals first second : SExpr) (different : first ≠ second) :
    Step base language
      (finishCall documentSpan start (definitionsCons head tail) lexicals (diagnostics [first, second]))
      (result (refused (diagnostics [first, second]))) ∧
    ¬ Step base language
      (finishCall documentSpan start (definitionsCons head tail) lexicals (diagnostics [first, second]))
      (result (refused (diagnostics [second, first]))) := by
  simp [finish_refused_diagnostics_step_iff, different, Ne.symm different]

end Mettapedia.GSLT.Parsing.PlainBnfValidationFinishSourceExecution
