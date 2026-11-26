import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataCompilationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataInventoryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.GSLT.LanguageDef.TopDownMatchDerivativeNormalization
import Mettapedia.OSLF.Framework.CarrierObjectClosureTransport

/-!
# Retained relative-control matcher source

The optional source realizes the normalized derivative cache, using the
existing obligation, goal and location wire. Each ordered instance retains
its announcement and displacement. Sharing applies to control activations;
it never quotients rule occurrences or absolute subject positions.

Fresh authored heads extend the retained matcher and guarded rule executor
conservatively. Their sources load exactly once. Helper
execution transports through the existing PeTTa program-agreement theorem.
The source quotation retains exact text but leaves reader adequacy as the
existing named boundary. Source execution implements overlap partitioning,
relative-path factoring, stable control interning, ordered cache activation
and matching with canonical binding completion. Completed execution agrees
with the canonical match list and retains the source's explicit derivative
dispatch count; that count excludes normalization, lookup and evaluator costs.

The first-order matching contract connects this source schedule to the original
ordered root dispatcher. First-order row admission and equation-free GSLT step
admission remain explicit; no broader scoped matcher or declaration-typing
claim follows from these matching and execution laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataNormalizedExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire OrderedPatternMatrixCompilation SubtermMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Equation)
open Eval
open Effects (State)
open MatchAutomataDerivativeExecution (positionTerm keyTerm obligationTerm locationTerm goalTerm optionTerm)
open MatchAutomataCompilationExecution (shapeTerm subjectTerm)
open MatchAutomataSourceExecution (listValue)
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_match_normalized.metta"
    sha256 "6d8b1e52cd08995c939516a78323655d0ba6412e63fea50dbd6856097d9a754a"

def program : Program := RuleExecutionProgram.program.append source.program

def equations (head : String) : List Equation :=
  program.equations.filter (fun equation => equation.head == head)

def matcherHead (head : String) : Bool :=
  RuleExecutionProgram.matcherHead head && !(head.startsWith "gslt:normalized:")

private theorem matcher_bodies_within :
    MatchAutomataProgram.program.equations.all (fun equation =>
      !matcherHead equation.head || codeWithin matcherHead equation.body) = true := by
  decide +kernel

theorem matcher_program_closed : ProgramClosed matcherHead MatchAutomataProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp matcher_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

private theorem extension_equations_fresh :
    ((RuleExecutionProgram.source.program.append RuleExecutionProgram.premiseSource.program).append
      source.program).equations.all (fun equation => !matcherHead equation.head) = true := by
  decide +kernel

private theorem extension_declarations_fresh :
    ((RuleExecutionProgram.source.program.append RuleExecutionProgram.premiseSource.program).append
      source.program).declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !matcherHead head
      | _ => true) = true := by
  decide +kernel

theorem matcher_program_agreement :
    ProgramAgreementOn matcherHead MatchAutomataProgram.program program := by
  have assembled : program = MatchAutomataProgram.program.append
      ((RuleExecutionProgram.source.program.append RuleExecutionProgram.premiseSource.program).append
        source.program) := by
    simp only [program, RuleExecutionProgram.program, SpaceSemantics.Program.append,
      List.append_assoc]
  rw [assembled]
  exact appended_program_agreement_of_checks _ _ _ extension_equations_fresh
    extension_declarations_fresh (fun _ _ => rfl)

theorem automata_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin matcherHead code = true)
    (checked : PureReturns MatchAutomataProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement matcher_program_closed matcher_program_agreement
    ⟨supported, rfl⟩ checked

/-- Conservative extension of the original guarded row dispatcher. -/
def ruleHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:normalized:")

private theorem rule_bodies_within :
    RuleExecutionProgram.program.equations.all (fun equation =>
      !ruleHead equation.head || codeWithin ruleHead equation.body) = true := by
  decide +kernel

theorem rule_program_closed : ProgramClosed ruleHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp rule_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

private theorem rule_extension_equations_fresh :
    source.program.equations.all (fun equation => !ruleHead equation.head) = true := by
  decide +kernel

private theorem rule_extension_declarations_fresh :
    source.program.declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !ruleHead head
      | _ => true) = true := by
  decide +kernel

theorem rule_program_agreement :
    ProgramAgreementOn ruleHead RuleExecutionProgram.program program := by
  exact appended_program_agreement_of_checks _ _ _ rule_extension_equations_fresh
    rule_extension_declarations_fresh (fun _ _ => rfl)

theorem rule_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin ruleHead code = true)
    (checked : PureReturns RuleExecutionProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement rule_program_closed rule_program_agreement
    ⟨supported, rfl⟩ checked

#print axioms rule_program_agreement
#print axioms rule_captured_returns

theorem no_initializers : source.program.initializers = [] := by decide +kernel

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

def instanceTerm (entry : TopDownMatchDerivativeNormalization.Instance) : Term :=
  .application "MInstance"
    [positionTerm entry.displacement, locationTerm entry.announcement, .natural entry.control]

def activationTerm (activation : Nat × Position) : Term :=
  .application "MActivation" [.natural activation.1, positionTerm activation.2]

def normalTerm (normal : TopDownMatchDerivativeNormalization.NormalForm Term) : Term :=
  .application "MNormal"
    [encodeList (encodeList obligationTerm) normal.controls, encodeList instanceTerm normal.instances]

def cacheTerm (entry : (Nat × Position) × Option (List (TopDownMatchDerivatives.Obligation Term))) : Term :=
  .application "MCache" [activationTerm entry.1, optionTerm entry.2]

def resultTerm (normal : TopDownMatchDerivativeNormalization.NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) : Term :=
  .application "MFinished"
    [encodeList goalTerm (TopDownMatchDerivativeNormalization.deriveShared normal observation),
      .natural (TopDownMatchDerivativeNormalization.activations normal).length]

private inductive PairHelper where
  | prefix | lookup | dispatch

private def PairHelper.head : PairHelper → String
  | .prefix => "gslt:normalized:strip-prefix"
  | .lookup => "gslt:normalized:lookup"
  | .dispatch => "gslt:normalized:dispatch"

private def PairHelper.first : PairHelper → String
  | .prefix => "base"
  | .lookup => "activation"
  | .dispatch => "instances"

private def PairHelper.second : PairHelper → String
  | .prefix => "path"
  | .lookup | .dispatch => "cache"

private def pairEquation (helper : PairHelper) : Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def pairEnvironment (helper : PairHelper) (left right : Term) : Subst :=
  [(helper.second, encoded right), (helper.first, encoded left)]

private theorem pair_clause (helper : PairHelper) (left right : Term) :
    clauses program helper.head [encoded left, encoded right] =
      [.evaluate (pairEnvironment helper left right) (pairEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  have unique : equations helper.head = [pairEquation helper] := by cases helper <;> rfl
  have formals : (pairEquation helper).arguments = [v helper.first, v helper.second] := by
    cases helper <;> decide +kernel
  rw [unique]
  cases helper <;> simp [formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
    pairEnvironment, PairHelper.first, PairHelper.second]

private theorem pair_call (helper : PairHelper) (bindings : Subst) (state : State)
    (left right : Term) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst bindings) = [encoded left, encoded right])
    (computed : PureReturns program (pairEnvironment helper left right) state
      (pairEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head arguments) state answer := by
  have length : arguments.length = 2 := by simpa using congrArg List.length captured
  apply PureData.raw_authored_call_return program bindings (pairEnvironment helper left right) state state
    helper.head arguments (pairEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide +kernel) _ _ computed
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact pair_clause helper left right

private theorem variable_pair_returns (bindings : Subst) (state : State)
    (one two : String) (left right : Atom)
    (first : applySubst bindings (v one) = left)
    (second : applySubst bindings (v two) = right) :
    PureReturns program bindings state (.expression [v one, v two]) state
      (.expression [left, right]) := by
  refine .step (step_transition rfl) ?_
  apply PureData.arguments_return program bindings state _ _
    (.cons ?_ (.cons ?_ .nil)) [] 0
  · simpa only [first] using variable_returns program bindings state one
  · simpa only [second] using variable_returns program bindings state two

private theorem some_template (name : String) :
    PureData.Template program (a "Some" [v name]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .captured _

/-- Encoding of the common-prefix remainder, not an additional matcher. -/
def prefixOptionTerm (base path : Position) : Term :=
  if base.isPrefixOf path then .application "Some" [positionTerm (path.drop base.length)]
  else .symbol "None"

private def prefixCons : Atom :=
  a "if" [a "==" [v "first", v "actual"],
    a "gslt:normalized:strip-prefix" [v "base-rest", v "path-rest"], .symbol "None"]

private def prefixCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", v "whole"], a "Some" [v "whole"]),
   (.expression [a "LCons" [v "first", v "base-rest"],
      a "LCons" [v "actual", v "path-rest"]], prefixCons),
   (v "bad", .symbol "None")]

private theorem prefix_shape : (pairEquation .prefix).body =
    a "case" [.expression [v "base", v "path"],
      .expression (prefixCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem prefix_body_returns (state : State) (base path : Position) :
    PureReturns program (pairEnvironment .prefix (positionTerm base) (positionTerm path)) state
      (pairEquation .prefix).body state (encoded (prefixOptionTerm base path)) := by
  induction base generalizing path with
  | nil =>
      let bindings := pairEnvironment .prefix (positionTerm []) (positionTerm path)
      let selected := ("whole", encoded (positionTerm path)) :: bindings
      rw [prefix_shape]
      apply case_returns program bindings selected state state state
        (.expression [v "base", v "path"])
        (.expression [encoded (positionTerm []), encoded (positionTerm path)])
        (a "Some" [v "whole"]) (encoded (prefixOptionTerm [] path)) _ prefixCases
        (read_cases_encoded _) _ _ _
      · apply variable_pair_returns <;>
          simp [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst, Subst.lookup]
      · simp [prefixCases, positionTerm, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second]
      · simpa [selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second,
          applySubst, applySubst.applySubstList, Subst.lookup, prefixOptionTerm,
          positionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          using PureData.template_return program selected state _ (some_template "whole")
  | cons first base ih =>
      cases path with
      | nil =>
          let bindings := pairEnvironment .prefix (positionTerm (first :: base)) (positionTerm [])
          let pair : Atom := .expression [encoded (positionTerm (first :: base)), encoded (positionTerm [])]
          let selected := ("bad", pair) :: bindings
          rw [prefix_shape]
          apply case_returns program bindings selected state state state
            (.expression [v "base", v "path"]) pair (.symbol "None")
            (encoded (prefixOptionTerm (first :: base) [])) _ prefixCases
            (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;>
              simp [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst, Subst.lookup]
          · simp [prefixCases, positionTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
              selected, pair, bindings, pairEnvironment, PairHelper.first, PairHelper.second]
          · simpa [prefixOptionTerm, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
      | cons actual path =>
          let bindings := pairEnvironment .prefix (positionTerm (first :: base)) (positionTerm (actual :: path))
          let selected := ("path-rest", encoded (positionTerm path)) ::
            ("actual", number actual) :: ("base-rest", encoded (positionTerm base)) ::
            ("first", number first) :: bindings
          rw [prefix_shape]
          apply case_returns program bindings selected state state state
            (.expression [v "base", v "path"])
            (.expression [encoded (positionTerm (first :: base)), encoded (positionTerm (actual :: path))])
            prefixCons (encoded (prefixOptionTerm (first :: base) (actual :: path))) _ prefixCases
            (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;>
              simp [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst, Subst.lookup]
          · simp [prefixCases, positionTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
              selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second]
          · apply if_returns program selected state state state
              (a "==" [v "first", v "actual"])
              (Effects.boolean (decide ((.natural first : Term) = .natural actual)))
              (a "gslt:normalized:strip-prefix" [v "base-rest", v "path-rest"])
              (.symbol "None") _
            · apply CettaWireAtom.equality_captured_returns <;> simp [selected, applySubst, Subst.lookup]
            · by_cases same : first = actual
              · subst actual
                have continuation := pair_call .prefix selected state (positionTerm base) (positionTerm path)
                  [v "base-rest", v "path-rest"] _
                  (by simp [selected, applySubst, Subst.lookup]) (ih path)
                simpa [prefixOptionTerm, PairHelper.head, Effects.boolean] using continuation
              · simpa [prefixOptionTerm, same, Effects.boolean, CettaWireAtom.encode] using
                  symbol_returns program selected state "None"

theorem prefix_returns (state : State) (base path : Position) :
    PureReturns program [] state
      (a "gslt:normalized:strip-prefix" [encoded (positionTerm base), encoded (positionTerm path)])
      state (encoded (prefixOptionTerm base path)) :=
  pair_call .prefix [] state _ _ _ _ (by simp) (prefix_body_returns state base path)

theorem prefix_captured_returns (bindings : Subst) (state : State) (base path : Position)
    (one two : Atom)
    (captured : [one, two].map (applySubst bindings) =
      [encoded (positionTerm base), encoded (positionTerm path)]) :
    PureReturns program bindings state (a "gslt:normalized:strip-prefix" [one, two]) state
      (encoded (prefixOptionTerm base path)) :=
  pair_call .prefix bindings state _ _ _ _ captured (prefix_body_returns state base path)

theorem activationTerm_injective : Function.Injective activationTerm := by
  intro left right same
  have arguments := (Term.application.inj same).2
  have indices := Term.natural.inj (List.cons.inj arguments).1
  have offsets := (List.cons.inj (List.cons.inj arguments).2).1
  have positions : left.2 = right.2 :=
    encodeList_injective Term.natural (fun _ _ equality => Term.natural.inj equality) offsets
  exact Prod.ext indices positions

private def relativeEquation : Equation :=
  (equations "gslt:normalized:relative")[0]'(by decide +kernel)

private def relativeEnvironment (base : Position) (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) : Subst :=
  [("pending", listValue (pending.map obligationTerm)), ("key", encoded (keyTerm observation.key)),
   ("position", encoded (positionTerm observation.position)), ("offset", encoded (positionTerm base))]

private theorem relative_clause (base : Position) (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    clauses program "gslt:normalized:relative"
      [encoded (positionTerm base), encoded (obligationTerm observation), listValue (pending.map obligationTerm)] =
      [.evaluate (relativeEnvironment base observation pending) relativeEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:relative").filterMap _ = _
  rw [show equations "gslt:normalized:relative" = [relativeEquation] from rfl]
  have formals : relativeEquation.arguments =
      [v "offset", a "Observe" [v "position", v "key"], v "pending"] := by decide +kernel
  simp [formals, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, relativeEnvironment]

private theorem relative_call (bindings : Subst) (state : State) (base : Position)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (obligationTerm observation), listValue (pending.map obligationTerm)])
    (computed : PureReturns program (relativeEnvironment base observation pending) state relativeEquation.body state
      (encoded (optionTerm (TopDownMatchDerivativeNormalization.relativeDerivative base observation pending)))) :
    PureReturns program bindings state (a "gslt:normalized:relative" arguments) state
      (encoded (optionTerm (TopDownMatchDerivativeNormalization.relativeDerivative base observation pending))) := by
  have length : arguments.length = 3 := by simpa using congrArg List.length captured
  apply PureData.raw_authored_call_return program bindings (relativeEnvironment base observation pending) state state
    "gslt:normalized:relative" arguments relativeEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ computed
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact relative_clause base observation pending

private def relativeCall : Atom :=
  a "gslt:automata:derive" [a "Observe" [v "relative", v "key"], v "pending"]
private def relativeCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "Some" [v "pending"]), (a "Some" [v "relative"], relativeCall)]

private theorem relative_shape : relativeEquation.body =
    a "case" [a "gslt:normalized:strip-prefix" [v "offset", v "position"],
      .expression (relativeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem relative_body_returns (state : State) (base : Position)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program (relativeEnvironment base observation pending) state relativeEquation.body state
      (encoded (optionTerm (TopDownMatchDerivativeNormalization.relativeDerivative base observation pending))) := by
  let bindings := relativeEnvironment base observation pending
  rw [relative_shape]
  by_cases below : base.IsPrefix observation.position
  · let relative : TopDownMatchDerivatives.Observation Term :=
      ⟨observation.position.drop base.length, observation.key⟩
    let selected := ("relative", encoded (positionTerm relative.position)) :: bindings
    apply case_returns program bindings selected state state state
      (a "gslt:normalized:strip-prefix" [v "offset", v "position"])
      (encoded (prefixOptionTerm base observation.position)) relativeCall _ _ relativeCases
      (read_cases_encoded _) _ _ _
    · apply prefix_captured_returns
      simp [bindings, relativeEnvironment, applySubst, Subst.lookup]
    · simp [relativeCases, prefixOptionTerm, List.isPrefixOf_iff_prefix.mpr below,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        Subst.lookup, selected, relative, bindings, relativeEnvironment]
    · have old := MatchAutomataDerivativeExecution.derive_captured_returns selected state relative pending
        [a "Observe" [v "relative", v "key"], v "pending"]
        (by simp [selected, bindings, relativeEnvironment, relative, applySubst,
          applySubst.applySubstList, Subst.lookup, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany])
      have returned := automata_captured_returns (by decide +kernel) old
      simpa [relativeCall, TopDownMatchDerivativeNormalization.relativeDerivative,
        TopDownMatchDerivativeNormalization.relativeObservation, List.isPrefixOf_iff_prefix.mpr below, relative]
        using returned
  · apply case_returns program bindings bindings state state state
      (a "gslt:normalized:strip-prefix" [v "offset", v "position"])
      (encoded (prefixOptionTerm base observation.position)) (a "Some" [v "pending"]) _ _ relativeCases
      (read_cases_encoded _) _ _ _
    · apply prefix_captured_returns
      simp [bindings, relativeEnvironment, applySubst, Subst.lookup]
    · simp [relativeCases, prefixOptionTerm, List.isPrefixOf_iff_prefix, below,
        CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · simpa [bindings, relativeEnvironment, applySubst, applySubst.applySubstList, Subst.lookup,
        TopDownMatchDerivativeNormalization.relativeDerivative,
        TopDownMatchDerivativeNormalization.relativeObservation, List.isPrefixOf_iff_prefix, below,
        optionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, listValue]
        using PureData.template_return program bindings state _ (some_template "pending")

theorem relative_returns (state : State) (base : Position)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program [] state
      (a "gslt:normalized:relative" [encoded (positionTerm base), encoded (obligationTerm observation),
        listValue (pending.map obligationTerm)]) state
      (encoded (optionTerm (TopDownMatchDerivativeNormalization.relativeDerivative base observation pending))) :=
  relative_call [] state base observation pending _ (by simp)
    (relative_body_returns state base observation pending)

theorem relative_captured_returns (bindings : Subst) (state : State) (base : Position)
    (observation : TopDownMatchDerivatives.Observation Term)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (obligationTerm observation), listValue (pending.map obligationTerm)]) :
    PureReturns program bindings state (a "gslt:normalized:relative" arguments) state
      (encoded (optionTerm (TopDownMatchDerivativeNormalization.relativeDerivative base observation pending))) :=
  relative_call bindings state base observation pending arguments captured
    (relative_body_returns state base observation pending)

private def termOptionTerm : Option Term → Term
  | none => .symbol "None"
  | some value => .application "Some" [value]

private def atEquation : Equation :=
  (equations "gslt:normalized:at")[0]'(by decide +kernel)

private def atEnvironment (values : List Term) (index : Nat) : Subst :=
  [("index", number index), ("values", listValue values)]

private theorem at_clause (values : List Term) (index : Nat) :
    clauses program "gslt:normalized:at" [listValue values, number index] =
      [.evaluate (atEnvironment values index) atEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:at").filterMap _ = _
  rw [show equations "gslt:normalized:at" = [atEquation] from rfl]
  have formals : atEquation.arguments = [v "values", v "index"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, atEnvironment]

private theorem at_call (bindings : Subst) (state : State) (values : List Term) (index : Nat)
    (argument indexCode : Atom) (captured : applySubst bindings argument = listValue values)
    (indexReturned : PureReturns program bindings state indexCode state (number index))
    (computed : PureReturns program (atEnvironment values index) state atEquation.body state
      (encoded (termOptionTerm values[index]?))) :
    PureReturns program bindings state (a "gslt:normalized:at" [argument, indexCode]) state
      (encoded (termOptionTerm values[index]?)) := by
  apply PureData.raw_prefix_authored_call_return program bindings (atEnvironment values index)
    state state state "gslt:normalized:at" [argument] [listValue values]
    indexCode (number index) atEquation.body _ (by decide) (by decide) (by decide +kernel)
    (by decide) _ (by simpa using (show argumentIsRaw program "gslt:normalized:at" 1 = false by decide +kernel))
    (by simp [captured]) indexReturned
    (at_clause values index) computed
  intro index bounded
  have zero : index = 0 := by simpa using bounded
  subst index
  decide +kernel

private def atCons : Atom :=
  a "if" [a "==" [v "index", number 0], a "Some" [v "first"],
    a "gslt:normalized:at" [v "rest", a "-" [v "index", number 1]]]

private def atCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"), (a "LCons" [v "first", v "rest"], atCons)]

private theorem at_shape : atEquation.body =
    a "case" [v "values", .expression (atCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem at_body_returns (state : State) (values : List Term) (index : Nat) :
    PureReturns program (atEnvironment values index) state atEquation.body state
      (encoded (termOptionTerm values[index]?)) := by
  induction values generalizing index with
  | nil =>
      rw [at_shape]
      apply case_returns program (atEnvironment [] index) (atEnvironment [] index)
        state state state (v "values") (listValue []) (.symbol "None") _ _ atCases
        (read_cases_encoded _) _ _ _
      · simpa [atEnvironment, applySubst, Subst.lookup] using
          variable_returns program (atEnvironment [] index) state "values"
      · simp [atCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [termOptionTerm, CettaWireAtom.encode] using
          symbol_returns program (atEnvironment [] index) state "None"
  | cons first rest ih =>
      let bindings := atEnvironment (first :: rest) index
      let selected := ("rest", listValue rest) :: ("first", encoded first) :: bindings
      rw [at_shape]
      apply case_returns program bindings selected state state state (v "values")
        (listValue (first :: rest)) atCons _ _ atCases (read_cases_encoded _) _ _ _
      · simpa [bindings, atEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "values"
      · simp [atCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, atEnvironment]
      · have compared : PureReturns program selected state (a "==" [v "index", number 0]) state
            (Effects.boolean (decide (index = 0))) := by
          simpa only [Term.natural.injEq] using
            CettaWireAtom.equality_evaluated_returns program selected state (.natural index) (.natural 0)
              (v "index") (number 0) (by decide +kernel) (by decide +kernel)
              (by simpa [selected, bindings, atEnvironment, applySubst, Subst.lookup] using
                variable_returns program selected state "index")
              (grounded_returns program selected state (.int 0))
        cases index with
        | zero =>
            apply if_returns program selected state state state _ (Effects.boolean true) _ _ _
              (by simpa using compared)
            simpa [termOptionTerm, selected, bindings, atEnvironment, applySubst,
              applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
              CettaWireAtom.encodeMany] using
              PureData.template_return program selected state _ (some_template "first")
        | succ index =>
            apply if_returns program selected state state state _ (Effects.boolean false) _ _ _
              (by simpa using compared)
            apply at_call selected state rest index (v "rest") (a "-" [v "index", number 1])
              (by simp [selected, applySubst, Subst.lookup]) _ (ih index)
            apply native_binary_call_returns program selected state state state state "-"
              (v "index") (number 1) (number (index + 1)) (number 1) (number index)
              (by decide) (by decide) (by decide +kernel) (by decide +kernel)
            · simpa [selected, bindings, atEnvironment, applySubst, Subst.lookup] using
                variable_returns program selected state "index"
            · exact grounded_returns program selected state (.int 1)
            · change (Except.ok (state, [Atom.grounded (.int (((index + 1 : Nat) : Int) - 1))]) :
                  Except Effects.Fault (State × List Atom)) =
                .ok (state, [Atom.grounded (.int (index : Int))])
              simp
            · decide

theorem at_captured_returns (bindings : Subst) (state : State) (values : List Term) (index : Nat)
    (argument indexCode : Atom) (captured : applySubst bindings argument = listValue values)
    (indexReturned : PureReturns program bindings state indexCode state (number index)) :
    PureReturns program bindings state (a "gslt:normalized:at" [argument, indexCode]) state
      (encoded (termOptionTerm values[index]?)) :=
  at_call bindings state values index argument indexCode captured indexReturned
    (at_body_returns state values index)

open TopDownMatchDerivativeNormalization (Instance NormalForm cachedDerivative relativeDerivative instantiate)

private inductive RawHelper where
  | activation | activations | cache | restore | derive
  | commonPrefix | gcp | dropDisplacement | relativePending | rebase
  | positionMember | overlapPending | overlaps | touches | partition | components
  | componentFor | pendingPositions | positions | base | factors | controls | index | instances | normalize
  | expandInstances | expand | execute | run | top | languageTop | languageRoot

private def RawHelper.head : RawHelper → String
  | .activation => "gslt:normalized:activation"
  | .activations => "gslt:normalized:activations"
  | .cache => "gslt:normalized:cache"
  | .restore => "gslt:normalized:restore"
  | .derive => "gslt:normalized:derive"
  | .commonPrefix => "gslt:normalized:common-prefix"
  | .gcp => "gslt:normalized:gcp"
  | .dropDisplacement => "gslt:normalized:drop-displacement"
  | .relativePending => "gslt:normalized:relative-pending"
  | .rebase => "gslt:normalized:rebase"
  | .positionMember => "gslt:normalized:position-member"
  | .overlapPending => "gslt:normalized:overlap-pending"
  | .overlaps => "gslt:normalized:overlaps"
  | .touches => "gslt:normalized:touches"
  | .partition => "gslt:normalized:partition"
  | .components => "gslt:normalized:components"
  | .componentFor => "gslt:normalized:component-for"
  | .pendingPositions => "gslt:normalized:pending-positions"
  | .positions => "gslt:normalized:positions"
  | .base => "gslt:normalized:base"
  | .factors => "gslt:normalized:factors"
  | .controls => "gslt:normalized:controls"
  | .index => "gslt:normalized:index"
  | .instances => "gslt:normalized:instances"
  | .normalize => "gslt:normalized:normalize"
  | .expandInstances => "gslt:normalized:expand-instances"
  | .expand => "gslt:normalized:expand"
  | .execute => "gslt:normalized:execute"
  | .run => "gslt:normalized:run"
  | .top => "gslt:normalized:top"
  | .languageTop => "gslt:normalized:language-top"
  | .languageRoot => "gslt:normalized:language-root-reducts"

private def RawHelper.arity : RawHelper → Nat
  | .activation | .activations => 1
  | .restore | .derive => 2
  | .cache | .languageRoot => 3
  | .gcp | .components | .pendingPositions | .positions | .base | .controls | .normalize | .expand => 1
  | .commonPrefix | .dropDisplacement | .relativePending | .rebase | .positionMember | .overlapPending
  | .overlaps | .touches | .partition | .componentFor | .factors | .index | .instances
  | .expandInstances | .execute | .run | .top | .languageTop => 2

private def rawEquation (helper : RawHelper) : Equation :=
  (source.program.equations.filter (fun equation => equation.head == helper.head))[0]'
    (by cases helper <;> decide +kernel)

set_option maxHeartbeats 1800000 in
private theorem raw_call (helper : RawHelper) (bindings callee : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (arity : values.length = helper.arity)
    (captured : arguments.map (applySubst bindings) = values)
    (selected : clauses program helper.head values = [.evaluate callee (rawEquation helper).body])
    (computed : PureReturns program callee state (rawEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head arguments) state answer := by
  have length : arguments.length = helper.arity := by
    simpa [arity] using congrArg List.length captured
  apply PureData.raw_authored_call_return program bindings callee state state
    helper.head arguments (rawEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide +kernel) _ _ computed
  · intro index bounded
    rw [length] at bounded
    have checked : (List.range helper.arity).all (argumentIsRaw program helper.head) = true := by
      cases helper <;> decide +kernel
    exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)
  · rw [captured]
    exact selected

private def activationEnvironment (entry : Instance) : Subst :=
  [("control", number entry.control), ("announcement", encoded (locationTerm entry.announcement)),
   ("offset", encoded (positionTerm entry.displacement))]

private theorem activation_clause (entry : Instance) :
    clauses program (RawHelper.activation.head) [encoded (instanceTerm entry)] =
      [.evaluate (activationEnvironment entry) (rawEquation .activation).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (RawHelper.activation.head)).filterMap _ = _
  rw [show equations (RawHelper.activation.head) = [rawEquation .activation] from rfl]
  have formals : (rawEquation .activation).arguments =
      [a "MInstance" [v "offset", v "announcement", v "control"]] := by decide +kernel
  simp [formals, instanceTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, activationEnvironment]

private theorem activation_template : PureData.Template program (a "MActivation" [v "control", v "offset"]) := by
  apply PureData.Template.constructor "MActivation" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem activation_captured_returns (bindings : Subst) (state : State) (entry : Instance)
    (argument : Atom) (captured : applySubst bindings argument = encoded (instanceTerm entry)) :
    PureReturns program bindings state (a "gslt:normalized:activation" [argument]) state
      (encoded (activationTerm entry.activation)) := by
  apply raw_call .activation bindings (activationEnvironment entry) state [argument] _ _ rfl
    (by simp [captured]) (activation_clause entry)
  have body : (rawEquation .activation).body = a "MActivation" [v "control", v "offset"] := by
    decide +kernel
  rw [body]
  simpa [activationEnvironment, activationTerm, Instance.activation, applySubst,
    applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    PureData.template_return program (activationEnvironment entry) state _ activation_template

private def activationsEnvironment (entries : List Instance) : Subst :=
  [("instances", listValue (entries.map instanceTerm))]

private theorem activations_clause (entries : List Instance) :
    clauses program (RawHelper.activations.head) [listValue (entries.map instanceTerm)] =
      [.evaluate (activationsEnvironment entries) (rawEquation .activations).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (RawHelper.activations.head)).filterMap _ = _
  rw [show equations (RawHelper.activations.head) = [rawEquation .activations] from rfl]
  have formals : (rawEquation .activations).arguments = [v "instances"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, activationsEnvironment]

private theorem activations_call (bindings : Subst) (state : State) (entries : List Instance)
    (argument : Atom) (captured : applySubst bindings argument = listValue (entries.map instanceTerm))
    (computed : PureReturns program (activationsEnvironment entries) state
      (rawEquation .activations).body state (listValue (entries.map fun entry => activationTerm entry.activation))) :
    PureReturns program bindings state (a "gslt:normalized:activations" [argument]) state
      (listValue (entries.map fun entry => activationTerm entry.activation)) :=
  raw_call .activations bindings (activationsEnvironment entries) state [argument] _ _ rfl
    (by simp [captured]) (activations_clause entries) computed

private def activationsCons : Atom :=
  a "let*" [.expression [.expression [v "activation", a "gslt:normalized:activation" [v "first"]],
      .expression [v "tail", a "gslt:normalized:activations" [v "rest"]]],
    a "LCons" [v "activation", v "tail"]]

private def activationsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "first", v "rest"], activationsCons)]

private theorem activations_shape : (rawEquation .activations).body =
    a "case" [v "instances", .expression (activationsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem activations_cons_template : PureData.Template program (a "LCons" [v "activation", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem activations_body_returns (state : State) (entries : List Instance) :
    PureReturns program (activationsEnvironment entries) state (rawEquation .activations).body state
      (listValue (entries.map fun entry => activationTerm entry.activation)) := by
  induction entries with
  | nil =>
      rw [activations_shape]
      apply case_returns program (activationsEnvironment []) (activationsEnvironment [])
        state state state (v "instances") (listValue []) (.symbol "LNil") _ _ activationsCases
        (read_cases_encoded _) _ _ _
      · simpa [activationsEnvironment, applySubst, Subst.lookup] using
          variable_returns program (activationsEnvironment []) state "instances"
      · simp [activationsCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program (activationsEnvironment []) state "LNil"
  | cons first rest ih =>
      let bindings := activationsEnvironment (first :: rest)
      let selected := ("rest", listValue (rest.map instanceTerm)) :: ("first", encoded (instanceTerm first)) :: bindings
      let activationBound := ("activation", encoded (activationTerm first.activation)) :: selected
      let tailBound := ("tail", listValue (rest.map fun entry => activationTerm entry.activation)) :: activationBound
      rw [activations_shape]
      apply case_returns program bindings selected state state state (v "instances")
        (listValue ((first :: rest).map instanceTerm)) activationsCons _ _ activationsCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, activationsEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "instances"
      · simp [activationsCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, activationsEnvironment]
      · apply PureData.let_bindings_return
          (program := program) (bindings := selected) (before := state) (middle := state)
          (pairs := [(v "activation", a "gslt:normalized:activation" [v "first"]),
            (v "tail", a "gslt:normalized:activations" [v "rest"])])
          (final := tailBound) _ state (a "LCons" [v "activation", v "tail"]) _ _
        · apply PureData.BindingsReturn.cons
            (bound := activationBound) (value := encoded (activationTerm first.activation))
          · exact activation_captured_returns selected state first (v "first")
              (by simp [selected, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              activationBound, selected, bindings, activationsEnvironment]
          · apply PureData.BindingsReturn.cons (bound := tailBound)
              (value := listValue (rest.map fun entry => activationTerm entry.activation))
            · exact activations_call activationBound state rest (v "rest")
                (by simp [activationBound, selected, applySubst, Subst.lookup]) ih
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                Subst.lookup, tailBound, activationBound, selected, bindings, activationsEnvironment]
            · exact .nil _ _
        · simpa [tailBound, activationBound, selected, listValue, encodeList, applySubst,
            applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program tailBound state _ activations_cons_template

theorem activations_captured_returns (bindings : Subst) (state : State) (entries : List Instance)
    (argument : Atom) (captured : applySubst bindings argument = listValue (entries.map instanceTerm)) :
    PureReturns program bindings state (a "gslt:normalized:activations" [argument]) state
      (listValue (entries.map fun entry => activationTerm entry.activation)) :=
  activations_call bindings state entries argument captured (activations_body_returns state entries)

private def lookupCons : Atom :=
  a "if" [a "==" [v "activation", v "key"], v "value",
    a "gslt:normalized:lookup" [v "activation", v "rest"]]

private def lookupCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
   (a "LCons" [a "MCache" [v "key", v "value"], v "rest"], lookupCons)]

private theorem lookup_shape : (pairEquation .lookup).body =
    a "case" [v "cache", .expression (lookupCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem lookup_body_returns (state : State) (activation : Nat × Position)
    (cache : List ((Nat × Position) × Option (List (TopDownMatchDerivatives.Obligation Term)))) :
    PureReturns program
      (pairEnvironment .lookup (activationTerm activation) (encodeList cacheTerm cache)) state
      (pairEquation .lookup).body state (encoded (optionTerm (cachedDerivative cache activation))) := by
  induction cache with
  | nil =>
      let bindings := pairEnvironment .lookup (activationTerm activation) (encodeList cacheTerm [])
      rw [lookup_shape]
      apply case_returns program bindings bindings state state state (v "cache") (listValue [])
        (.symbol "None") _ _ lookupCases (read_cases_encoded _) _ _ _
      · simpa [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst,
          Subst.lookup, listValue] using variable_returns program bindings state "cache"
      · simp [lookupCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | cons first rest ih =>
      let bindings := pairEnvironment .lookup (activationTerm activation) (encodeList cacheTerm (first :: rest))
      let selected := ("rest", encoded (encodeList cacheTerm rest)) ::
        ("value", encoded (optionTerm first.2)) :: ("key", encoded (activationTerm first.1)) :: bindings
      rw [lookup_shape]
      apply case_returns program bindings selected state state state (v "cache")
        (encoded (encodeList cacheTerm (first :: rest))) lookupCons _ _ lookupCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst,
          Subst.lookup] using variable_returns program bindings state "cache"
      · simp [lookupCases, cacheTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second]
      · have compared : PureReturns program selected state
            (a "==" [v "activation", v "key"]) state (Effects.boolean (decide (first.1 = activation))) := by
          simpa only [activationTerm_injective.eq_iff, eq_comm] using
            CettaWireAtom.equality_captured_returns program selected state
              (activationTerm activation) (activationTerm first.1) "activation" "key"
              (by simp [selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second,
                applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
        by_cases same : first.1 = activation
        · apply if_returns program selected state state state _ (Effects.boolean true) _ _ _
            (by simpa [same] using compared)
          simpa [cachedDerivative, same, selected, applySubst, Subst.lookup] using
            variable_returns program selected state "value"
        · apply if_returns program selected state state state _ (Effects.boolean false) _ _ _
            (by simpa [same] using compared)
          simpa [cachedDerivative, same, Effects.boolean, PairHelper.head] using
            pair_call .lookup selected state (activationTerm activation) (encodeList cacheTerm rest)
              [v "activation", v "rest"] _
              (by simp [selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second,
                applySubst, Subst.lookup]) ih

theorem lookup_captured_returns (bindings : Subst) (state : State) (activation : Nat × Position)
    (cache : List ((Nat × Position) × Option (List (TopDownMatchDerivatives.Obligation Term))))
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (activationTerm activation), encoded (encodeList cacheTerm cache)]) :
    PureReturns program bindings state (a "gslt:normalized:lookup" arguments) state
      (encoded (optionTerm (cachedDerivative cache activation))) :=
  pair_call .lookup bindings state (activationTerm activation) (encodeList cacheTerm cache)
    arguments _ captured (lookup_body_returns state activation cache)

private def restoreEnvironment (entry : Instance)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) : Subst :=
  [("pending", listValue (pending.map obligationTerm)), ("index", number entry.control),
   ("occurrence", number entry.announcement.occurrence),
   ("relative", encoded (positionTerm entry.announcement.position)),
   ("offset", encoded (positionTerm entry.displacement))]

private theorem restore_clause (entry : Instance) (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    clauses program (RawHelper.restore.head)
      [encoded (instanceTerm entry), listValue (pending.map obligationTerm)] =
      [.evaluate (restoreEnvironment entry pending) (rawEquation .restore).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (RawHelper.restore.head)).filterMap _ = _
  rw [show equations (RawHelper.restore.head) = [rawEquation .restore] from rfl]
  have formals : (rawEquation .restore).arguments =
      [a "MInstance" [v "offset", a "At" [v "relative", v "occurrence"], v "index"], v "pending"] := by
    decide +kernel
  simp [formals, instanceTerm, locationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, restoreEnvironment]

private def restorePairs : List (Atom × Atom) :=
  [(v "position", a "gslt:automata:append" [v "offset", v "relative"]),
   (v "absolute", a "gslt:automata:shift" [v "offset", v "pending"])]

private def restoreResult : Atom := a "MGoal" [a "At" [v "position", v "occurrence"], v "absolute"]

private theorem restore_shape : (rawEquation .restore).body =
    a "let*" [.expression (restorePairs.map fun row => .expression [row.1, row.2]), restoreResult] := by
  decide +kernel

private theorem restore_template : PureData.Template program restoreResult := by
  apply PureData.Template.constructor "MGoal" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "At" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem restore_captured_returns (bindings : Subst) (state : State) (entry : Instance)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (instanceTerm entry), listValue (pending.map obligationTerm)]) :
    PureReturns program bindings state (a "gslt:normalized:restore" arguments) state
      (encoded (goalTerm (instantiate entry pending))) := by
  apply raw_call .restore bindings (restoreEnvironment entry pending) state arguments _ _ rfl
    captured (restore_clause entry pending)
  let callee := restoreEnvironment entry pending
  let position := encoded (positionTerm (entry.displacement ++ entry.announcement.position))
  let positionBound := ("position", position) :: callee
  let absolute := listValue ((TopDownMatchDerivatives.shift entry.displacement pending).map obligationTerm)
  let absoluteBound := ("absolute", absolute) :: positionBound
  rw [restore_shape]
  apply PureData.let_bindings_return (program := program) (bindings := callee)
    (before := state) (middle := state) (pairs := restorePairs) (final := absoluteBound)
    _ state restoreResult _ _
  · apply PureData.BindingsReturn.cons (bound := positionBound) (value := position)
    · have old := MatchAutomataSourceExecution.append_captured_returns callee state
        (entry.displacement.map Term.natural) (entry.announcement.position.map Term.natural)
        (v "offset") (v "relative")
        (by simp [callee, restoreEnvironment, applySubst, Subst.lookup, positionTerm, listValue])
      have same : encodeList id (entry.displacement.map Term.natural ++
          entry.announcement.position.map Term.natural) =
          positionTerm (entry.displacement ++ entry.announcement.position) := by
        rw [← List.map_append, encodeList_map]
        rfl
      have returned := automata_captured_returns (by decide +kernel) old
      change PureReturns program callee state (a "gslt:automata:append" [v "offset", v "relative"])
        state (encoded (encodeList id (entry.displacement.map Term.natural ++
          entry.announcement.position.map Term.natural))) at returned
      rw [same] at returned
      exact returned
    · simp [positionBound, callee, restoreEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := absoluteBound) (value := absolute)
      · exact automata_captured_returns (by decide +kernel)
          (MatchAutomataCompilationExecution.shift_captured_returns positionBound state
            entry.displacement pending (v "offset") (v "pending")
            (by simp [positionBound, callee, restoreEnvironment, applySubst, Subst.lookup])
            (by simp [positionBound, callee, restoreEnvironment, applySubst, Subst.lookup]))
      · simp [absoluteBound, positionBound, callee, restoreEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · exact .nil _ _
  · simpa [restoreResult, instantiate, TopDownMatchDerivativeNormalization.restore, goalTerm,
      locationTerm, position, absolute, positionBound, absoluteBound, callee, restoreEnvironment,
      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, listValue] using
      PureData.template_return program absoluteBound state _ restore_template

private def cacheEnvironment (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (activations : List (Nat × Position)) : Subst :=
  [("activations", listValue (activations.map activationTerm)),
   ("observation", encoded (obligationTerm observation)),
   ("controls", encoded (encodeList (encodeList obligationTerm) normal.controls))]

private def cacheRows (normal : NormalForm Term) (observation : TopDownMatchDerivatives.Observation Term)
    (activations : List (Nat × Position)) :=
  activations.map fun activation =>
    (activation, TopDownMatchDerivativeNormalization.activationDerivative normal observation activation)

private theorem cache_clause (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (activations : List (Nat × Position)) :
    clauses program (RawHelper.cache.head)
      [encoded (encodeList (encodeList obligationTerm) normal.controls), encoded (obligationTerm observation),
       listValue (activations.map activationTerm)] =
      [.evaluate (cacheEnvironment normal observation activations) (rawEquation .cache).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (RawHelper.cache.head)).filterMap _ = _
  rw [show equations (RawHelper.cache.head) = [rawEquation .cache] from rfl]
  have formals : (rawEquation .cache).arguments = [v "controls", v "observation", v "activations"] := by
    decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, cacheEnvironment]

private theorem cache_call (bindings : Subst) (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (activations : List (Nat × Position))
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList obligationTerm) normal.controls), encoded (obligationTerm observation),
       listValue (activations.map activationTerm)])
    (computed : PureReturns program (cacheEnvironment normal observation activations) state
      (rawEquation .cache).body state (encoded (encodeList cacheTerm (cacheRows normal observation activations)))) :
    PureReturns program bindings state (a "gslt:normalized:cache" arguments) state
      (encoded (encodeList cacheTerm (cacheRows normal observation activations))) :=
  raw_call .cache bindings (cacheEnvironment normal observation activations) state arguments _ _ rfl
    captured (cache_clause normal observation activations) computed

private def cacheConsResult (payload : Atom) : Atom :=
  a "LCons" [a "MCache" [a "MActivation" [v "index", v "offset"], payload], v "tail"]

private def cacheSome : Atom :=
  a "let" [v "derivative", a "gslt:normalized:relative" [v "offset", v "observation", v "pending"],
    cacheConsResult (v "derivative")]

private def cacheSelectionCases : SpaceSemantics.Cases :=
  [(.symbol "None", cacheConsResult (.symbol "None")), (a "Some" [v "pending"], cacheSome)]

private def cacheSelection : Atom :=
  a "case" [a "gslt:normalized:at" [v "controls", v "index"],
    .expression (cacheSelectionCases.map fun row => .expression [row.1, row.2])]

private def cacheCons : Atom :=
  a "let" [v "tail", a "gslt:normalized:cache" [v "controls", v "observation", v "rest"], cacheSelection]

private def cacheCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "MActivation" [v "index", v "offset"], v "rest"], cacheCons)]

private theorem cache_shape : (rawEquation .cache).body =
    a "case" [v "activations", .expression (cacheCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem cache_cons_template (payload : Atom) (literal : PureData.Template program payload) :
    PureData.Template program (cacheConsResult payload) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "MCache" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply PureData.Template.constructor "MActivation" _ (by decide +kernel) (by decide)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .captured _
    · exact literal
  · exact .captured _

private theorem cache_body_returns (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (activations : List (Nat × Position)) :
    PureReturns program (cacheEnvironment normal observation activations) state (rawEquation .cache).body state
      (encoded (encodeList cacheTerm (cacheRows normal observation activations))) := by
  induction activations with
  | nil =>
      let bindings := cacheEnvironment normal observation []
      rw [cache_shape]
      apply case_returns program bindings bindings state state state (v "activations") (listValue [])
        (.symbol "LNil") _ _ cacheCases (read_cases_encoded _) _ _ _
      · simpa [bindings, cacheEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "activations"
      · simp [cacheCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := cacheEnvironment normal observation (first :: rest)
      let selected := ("rest", listValue (rest.map activationTerm)) ::
        ("offset", encoded (positionTerm first.2)) :: ("index", number first.1) :: bindings
      let tail := encoded (encodeList cacheTerm (cacheRows normal observation rest))
      let tailBound := ("tail", tail) :: selected
      rw [cache_shape]
      apply case_returns program bindings selected state state state (v "activations")
        (listValue ((first :: rest).map activationTerm)) cacheCons _ _ cacheCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, cacheEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "activations"
      · simp [cacheCases, activationTerm, listValue, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
          bindings, cacheEnvironment]
      · apply let_returns program selected tailBound state state state (v "tail")
          (a "gslt:normalized:cache" [v "controls", v "observation", v "rest"]) cacheSelection tail _
        · exact cache_call selected state normal observation rest _
            (by simp [selected, bindings, cacheEnvironment, applySubst, Subst.lookup]) ih
        · simp [tailBound, selected, bindings, cacheEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · have atReturned := at_captured_returns tailBound state
            (normal.controls.map (encodeList obligationTerm)) first.1 (v "controls") (v "index")
            (by simp [tailBound, selected, bindings, cacheEnvironment, applySubst, Subst.lookup,
              listValue, encodeList_map])
            (by simpa [tailBound, selected, applySubst, Subst.lookup] using
              variable_returns program tailBound state "index")
          cases chosen : normal.controls[first.1]? with
          | none =>
              apply case_returns program tailBound tailBound state state state
                (a "gslt:normalized:at" [v "controls", v "index"]) (.symbol "None")
                (cacheConsResult (.symbol "None")) _ _ cacheSelectionCases
                (read_cases_encoded _) _ _ _
              · simpa [List.getElem?_map, chosen, termOptionTerm, CettaWireAtom.encode] using atReturned
              · simp [cacheSelectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [cacheConsResult, cacheRows, TopDownMatchDerivativeNormalization.activationDerivative,
                  chosen, cacheTerm, activationTerm, optionTerm, tail, tailBound, selected,
                  applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, encodeList] using
                  PureData.template_return program tailBound state _
                    (cache_cons_template (.symbol "None") (.symbol _))
          | some pending =>
              let pendingBound := ("pending", listValue (pending.map obligationTerm)) :: tailBound
              let derivative := encoded (optionTerm (relativeDerivative first.2 observation pending))
              let derivativeBound := ("derivative", derivative) :: pendingBound
              apply case_returns program tailBound pendingBound state state state
                (a "gslt:normalized:at" [v "controls", v "index"])
                (encoded (optionTerm (some pending))) cacheSome _ _ cacheSelectionCases
                (read_cases_encoded _) _ _ _
              · simpa [List.getElem?_map, chosen, termOptionTerm, optionTerm] using atReturned
              · simp [cacheSelectionCases, optionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, pendingBound, tailBound, selected, bindings,
                  cacheEnvironment, listValue, encodeList_map]
              · apply let_returns program pendingBound derivativeBound state state state (v "derivative")
                  (a "gslt:normalized:relative" [v "offset", v "observation", v "pending"])
                  (cacheConsResult (v "derivative")) derivative _
                · exact relative_captured_returns pendingBound state first.2 observation pending _
                    (by simp [pendingBound, tailBound, selected, bindings, cacheEnvironment, applySubst, Subst.lookup])
                · simp [derivativeBound, pendingBound, tailBound, selected, bindings, cacheEnvironment,
                    SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                · simpa [cacheConsResult, cacheRows, TopDownMatchDerivativeNormalization.activationDerivative,
                    chosen, cacheTerm, activationTerm, tail, tailBound, selected, pendingBound,
                    derivative, derivativeBound, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList] using
                    PureData.template_return program derivativeBound state _
                      (cache_cons_template (v "derivative") (.captured _))

theorem cache_captured_returns (bindings : Subst) (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (activations : List (Nat × Position))
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList obligationTerm) normal.controls), encoded (obligationTerm observation),
       listValue (activations.map activationTerm)]) :
    PureReturns program bindings state (a "gslt:normalized:cache" arguments) state
      (encoded (encodeList cacheTerm (cacheRows normal observation activations))) :=
  cache_call bindings state normal observation activations arguments captured
    (cache_body_returns state normal observation activations)

private def dispatchSelectionCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"),
   (a "Some" [v "pending"], a "let" [v "restored", a "gslt:normalized:restore" [v "first", v "pending"],
      a "LCons" [v "restored", v "tail"]])]

private def dispatchSelection : Atom :=
  a "case" [a "gslt:normalized:lookup" [v "activation", v "cache"],
    .expression (dispatchSelectionCases.map fun row => .expression [row.1, row.2])]

private def dispatchPairs : List (Atom × Atom) :=
  [(v "tail", a "gslt:normalized:dispatch" [v "rest", v "cache"]),
   (v "activation", a "gslt:normalized:activation" [v "first"])]

private def dispatchCons : Atom :=
  a "let*" [.expression (dispatchPairs.map fun row => .expression [row.1, row.2]), dispatchSelection]

private def dispatchCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "first", v "rest"], dispatchCons)]

private theorem dispatch_shape : (pairEquation .dispatch).body =
    a "case" [v "instances", .expression (dispatchCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem dispatch_cons_template : PureData.Template program (a "LCons" [v "restored", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem dispatch_body_returns (state : State) (entries : List Instance)
    (cache : List ((Nat × Position) × Option (List (TopDownMatchDerivatives.Obligation Term)))) :
    PureReturns program
      (pairEnvironment .dispatch (encodeList instanceTerm entries) (encodeList cacheTerm cache)) state
      (pairEquation .dispatch).body state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.dispatch ⟨[], entries⟩ cache))) := by
  induction entries with
  | nil =>
      let bindings := pairEnvironment .dispatch (encodeList instanceTerm []) (encodeList cacheTerm cache)
      rw [dispatch_shape]
      apply case_returns program bindings bindings state state state (v "instances") (listValue [])
        (.symbol "LNil") _ _ dispatchCases (read_cases_encoded _) _ _ _
      · simpa [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst,
          Subst.lookup, listValue] using variable_returns program bindings state "instances"
      · simp [dispatchCases, listValue, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := pairEnvironment .dispatch (encodeList instanceTerm (first :: rest)) (encodeList cacheTerm cache)
      let selected := ("rest", encoded (encodeList instanceTerm rest)) :: ("first", encoded (instanceTerm first)) :: bindings
      let tail := encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.dispatch ⟨[], rest⟩ cache))
      let tailBound := ("tail", tail) :: selected
      let activationBound := ("activation", encoded (activationTerm first.activation)) :: tailBound
      rw [dispatch_shape]
      apply case_returns program bindings selected state state state (v "instances")
        (encoded (encodeList instanceTerm (first :: rest))) dispatchCons _ _ dispatchCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, pairEnvironment, PairHelper.first, PairHelper.second, applySubst,
          Subst.lookup] using variable_returns program bindings state "instances"
      · simp [dispatchCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second]
      · apply PureData.let_bindings_return (program := program) (bindings := selected)
          (before := state) (middle := state) (pairs := dispatchPairs) (final := activationBound)
          _ state dispatchSelection _ _
        · apply PureData.BindingsReturn.cons (bound := tailBound) (value := tail)
          · exact pair_call .dispatch selected state (encodeList instanceTerm rest) (encodeList cacheTerm cache)
              [v "rest", v "cache"] _
              (by simp [selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second,
                applySubst, Subst.lookup]) ih
          · simp [tailBound, selected, bindings, pairEnvironment, PairHelper.first, PairHelper.second,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := activationBound)
              (value := encoded (activationTerm first.activation))
            · exact activation_captured_returns tailBound state first (v "first")
                (by simp [tailBound, selected, applySubst, Subst.lookup])
            · simp [activationBound, tailBound, selected, bindings, pairEnvironment,
                PairHelper.first, PairHelper.second, SpaceSemantics.matchBinding,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact .nil _ _
        · have lookupReturned := lookup_captured_returns activationBound state first.activation cache
            [v "activation", v "cache"]
            (by simp [activationBound, tailBound, selected, bindings, pairEnvironment,
              PairHelper.first, PairHelper.second, applySubst, Subst.lookup])
          cases picked : cachedDerivative cache first.activation with
          | none =>
              apply case_returns program activationBound activationBound state state state
                (a "gslt:normalized:lookup" [v "activation", v "cache"]) (.symbol "None")
                (v "tail") _ _ dispatchSelectionCases (read_cases_encoded _) _ _ _
              · simpa [picked, optionTerm, CettaWireAtom.encode] using lookupReturned
              · simp [dispatchSelectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [TopDownMatchDerivativeNormalization.dispatch, picked, activationBound, tailBound,
                  tail, applySubst, Subst.lookup] using variable_returns program activationBound state "tail"
          | some pending =>
              let pendingBound := ("pending", listValue (pending.map obligationTerm)) :: activationBound
              let restored := encoded (goalTerm (instantiate first pending))
              let restoredBound := ("restored", restored) :: pendingBound
              apply case_returns program activationBound pendingBound state state state
                (a "gslt:normalized:lookup" [v "activation", v "cache"])
                (encoded (optionTerm (some pending)))
                (a "let" [v "restored", a "gslt:normalized:restore" [v "first", v "pending"],
                  a "LCons" [v "restored", v "tail"]]) _ _ dispatchSelectionCases
                (read_cases_encoded _) _ _ _
              · simpa [picked] using lookupReturned
              · simp [dispatchSelectionCases, optionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, pendingBound, activationBound, tailBound, selected, bindings,
                  pairEnvironment, PairHelper.first, PairHelper.second, listValue, encodeList_map]
              · apply let_returns program pendingBound restoredBound state state state (v "restored")
                  (a "gslt:normalized:restore" [v "first", v "pending"])
                  (a "LCons" [v "restored", v "tail"]) restored _
                · exact restore_captured_returns pendingBound state first pending _
                    (by simp [pendingBound, activationBound, tailBound, selected, applySubst, Subst.lookup])
                · simp [restoredBound, pendingBound, activationBound, tailBound, selected, bindings,
                    pairEnvironment, PairHelper.first, PairHelper.second, SpaceSemantics.matchBinding,
                    SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                · simpa [TopDownMatchDerivativeNormalization.dispatch, picked, encodeList,
                    restoredBound, restored, pendingBound, activationBound, tailBound, tail, applySubst,
                    applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return program restoredBound state _ dispatch_cons_template

theorem dispatch_captured_returns (bindings : Subst) (state : State) (normal : NormalForm Term)
    (cache : List ((Nat × Position) × Option (List (TopDownMatchDerivatives.Obligation Term))))
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList instanceTerm normal.instances), encoded (encodeList cacheTerm cache)]) :
    PureReturns program bindings state (a "gslt:normalized:dispatch" arguments) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.dispatch normal cache))) := by
  exact pair_call .dispatch bindings state (encodeList instanceTerm normal.instances)
    (encodeList cacheTerm cache) arguments _ captured (dispatch_body_returns state normal.instances cache)

theorem encoded_activations (normal : NormalForm Term) :
    (normal.instances.map fun entry => activationTerm entry.activation).eraseDups =
      (TopDownMatchDerivativeNormalization.activations normal).map activationTerm := by
  rw [show (normal.instances.map fun entry => activationTerm entry.activation) =
      (normal.instances.map Instance.activation).map activationTerm by simp [List.map_map]]
  exact Mettapedia.OSLF.Framework.CarrierObjectClosure.eraseDups_map_of_injective
    activationTerm activationTerm_injective _

private def deriveEnvironment (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) : Subst :=
  [("observation", encoded (obligationTerm observation)),
   ("instances", encoded (encodeList instanceTerm normal.instances)),
   ("controls", encoded (encodeList (encodeList obligationTerm) normal.controls))]

private theorem derive_clause (normal : NormalForm Term) (observation : TopDownMatchDerivatives.Observation Term) :
    clauses program (RawHelper.derive.head) [encoded (normalTerm normal), encoded (obligationTerm observation)] =
      [.evaluate (deriveEnvironment normal observation) (rawEquation .derive).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (RawHelper.derive.head)).filterMap _ = _
  rw [show equations (RawHelper.derive.head) = [rawEquation .derive] from rfl]
  have formals : (rawEquation .derive).arguments =
      [a "MNormal" [v "controls", v "instances"], v "observation"] := by decide +kernel
  simp [formals, normalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, deriveEnvironment]

private def derivePairs : List (Atom × Atom) :=
  [(v "raw", a "gslt:normalized:activations" [v "instances"]),
   (v "activations", a "gslt:automata:unique" [v "raw"]),
   (v "cache", a "gslt:normalized:cache" [v "controls", v "observation", v "activations"]),
   (v "goals", a "gslt:normalized:dispatch" [v "instances", v "cache"]),
   (v "count", a "gslt:automata:length" [v "cache"])]

private def deriveResult : Atom := a "MFinished" [v "goals", v "count"]

private theorem derive_shape : (rawEquation .derive).body =
    a "let*" [.expression (derivePairs.map fun row => .expression [row.1, row.2]), deriveResult] := by
  decide +kernel

private theorem derive_result_template : PureData.Template program deriveResult := by
  apply PureData.Template.constructor "MFinished" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem derive_body_returns (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) :
    PureReturns program (deriveEnvironment normal observation) state (rawEquation .derive).body state
      (encoded (resultTerm normal observation)) := by
  let bindings := deriveEnvironment normal observation
  let raw := listValue (normal.instances.map fun entry => activationTerm entry.activation)
  let rawBound := ("raw", raw) :: bindings
  let activations := TopDownMatchDerivativeNormalization.activations normal
  let activationsBound := ("activations", listValue (activations.map activationTerm)) :: rawBound
  let cache := TopDownMatchDerivativeNormalization.derivativeCache normal observation
  let cacheBound := ("cache", encoded (encodeList cacheTerm cache)) :: activationsBound
  let goals := TopDownMatchDerivativeNormalization.deriveShared normal observation
  let goalsBound := ("goals", encoded (encodeList goalTerm goals)) :: cacheBound
  let countBound := ("count", number activations.length) :: goalsBound
  rw [derive_shape]
  apply PureData.let_bindings_return (program := program) (bindings := bindings)
    (before := state) (middle := state) (pairs := derivePairs) (final := countBound)
    _ state deriveResult _ _
  · apply PureData.BindingsReturn.cons (bound := rawBound) (value := raw)
    · exact activations_captured_returns bindings state normal.instances (v "instances")
        (by simp [bindings, deriveEnvironment, applySubst, Subst.lookup, listValue, encodeList_map])
    · simp [rawBound, bindings, deriveEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := activationsBound)
        (value := listValue (activations.map activationTerm))
      · have old := MatchAutomataInventoryExecution.unique_captured_returns rawBound state
          (normal.instances.map fun entry => activationTerm entry.activation) (v "raw")
          (by simp [rawBound, raw, applySubst, Subst.lookup])
        rw [encoded_activations] at old
        exact automata_captured_returns (by decide +kernel) old
      · simp [activationsBound, rawBound, bindings, deriveEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := cacheBound) (value := encoded (encodeList cacheTerm cache))
        · exact cache_captured_returns activationsBound state normal observation activations _
            (by simp [activationsBound, rawBound, bindings, deriveEnvironment, applySubst, Subst.lookup])
        · simp [cacheBound, activationsBound, rawBound, bindings, deriveEnvironment,
            SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := goalsBound) (value := encoded (encodeList goalTerm goals))
          · exact dispatch_captured_returns cacheBound state normal cache _
              (by simp [cacheBound, activationsBound, rawBound, bindings, deriveEnvironment, applySubst, Subst.lookup])
          · simp [goalsBound, cacheBound, activationsBound, rawBound, bindings, deriveEnvironment,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := countBound) (value := number activations.length)
            · have old := MatchAutomataSourceExecution.length_captured_returns goalsBound state
                (cache.map cacheTerm) (v "cache")
                (by simp [goalsBound, cacheBound, applySubst, Subst.lookup, listValue, encodeList_map])
              simpa [cache, TopDownMatchDerivativeNormalization.derivativeCache, activations] using
                automata_captured_returns (by decide +kernel) old
            · simp [countBound, goalsBound, cacheBound, activationsBound, rawBound, bindings,
                deriveEnvironment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact .nil _ _
  · simpa [deriveResult, resultTerm, countBound, goalsBound, goals, activations, applySubst,
      applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program countBound state _ derive_result_template

/-- The retained optional source computes the cached derivative exactly.
The counter measures unique cache activations; it excludes normalization,
lookup, lowering, allocation and evaluator overhead. -/
theorem derivative_captured_returns (bindings : Subst) (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (normalTerm normal), encoded (obligationTerm observation)]) :
    PureReturns program bindings state (a "gslt:normalized:derive" arguments) state
      (encoded (resultTerm normal observation)) :=
  raw_call .derive bindings (deriveEnvironment normal observation) state arguments _ _ rfl captured
    (derive_clause normal observation) (derive_body_returns state normal observation)

theorem derivative_returns (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) :
    PureReturns program [] state
      (a "gslt:normalized:derive" [encoded (normalTerm normal), encoded (obligationTerm observation)]) state
      (encoded (resultTerm normal observation)) :=
  derivative_captured_returns [] state normal observation _ (by simp)

theorem derivative_completed_iff (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      { state, control := .evaluate []
          (a "gslt:normalized:derive" [encoded (normalTerm normal), encoded (obligationTerm observation)]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm normal observation)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (derivative_returns state normal observation)
    after answers input output

theorem derivative_derivation_iff (state : State) (normal : NormalForm Term)
    (observation : TopDownMatchDerivatives.Observation Term) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (a "gslt:normalized:derive" [encoded (normalTerm normal), encoded (obligationTerm observation)]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm normal observation)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (derivative_returns state normal observation)
    after answers input output

/-- Paper-normalized source goals retain the exact old derivative goal vector,
including occurrence order, duplicate announcements, absolute positions and
failure. Source execution is the proved computation above, rather than a
new reference definition. -/
theorem derivative_normalize_returns (state : State) (goals : List (TopDownMatchDerivatives.Goal Term))
    (observation : TopDownMatchDerivatives.Observation Term) :
    PureReturns program [] state
      (a "gslt:normalized:derive"
        [encoded (normalTerm (TopDownMatchDerivativeNormalization.normalize goals)), encoded (obligationTerm observation)])
      state
      (encoded (.application "MFinished"
        [encodeList goalTerm (TopDownMatchDerivatives.deriveGoals observation goals),
         .natural (TopDownMatchDerivativeNormalization.activations
           (TopDownMatchDerivativeNormalization.normalize goals)).length])) := by
  simpa [resultTerm, TopDownMatchDerivativeNormalization.deriveShared_eq_deriveGoals,
    TopDownMatchDerivativeNormalization.expand_normalize] using
    derivative_returns state (TopDownMatchDerivativeNormalization.normalize goals) observation

private theorem raw_unique (helper : RawHelper) : equations helper.head = [rawEquation helper] := by
  cases helper <;> rfl

private def unaryEnvironment (name : String) (value : Atom) : Subst := [(name, value)]
private def binaryEnvironment (first second : String) (left right : Atom) : Subst :=
  [(second, right), (first, left)]

private theorem unary_clause (helper : RawHelper) (name : String) (value : Atom)
    (formals : (rawEquation helper).arguments = [v name]) :
    clauses program helper.head [value] =
      [.evaluate (unaryEnvironment name value) (rawEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [raw_unique]
  simp [formals, unaryEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem binary_clause (helper : RawHelper) (first second : String) (left right : Atom)
    (different : first ≠ second) (formals : (rawEquation helper).arguments = [v first, v second]) :
    clauses program helper.head [left, right] =
      [.evaluate (binaryEnvironment first second left right) (rawEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [raw_unique]
  simp [formals, binaryEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, different]

private theorem unary_call (helper : RawHelper) (name : String) (bindings : Subst) (state : State)
    (argument value answer : Atom) (arity : helper.arity = 1)
    (formals : (rawEquation helper).arguments = [v name])
    (captured : applySubst bindings argument = value)
    (computed : PureReturns program (unaryEnvironment name value) state (rawEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head [argument]) state answer :=
  raw_call helper bindings (unaryEnvironment name value) state [argument] [value] answer
    (by simp [arity]) (by simp [captured]) (unary_clause helper name value formals) computed

private theorem binary_call (helper : RawHelper) (first second : String) (bindings : Subst) (state : State)
    (arguments : List Atom) (left right answer : Atom) (arity : helper.arity = 2)
    (different : first ≠ second) (formals : (rawEquation helper).arguments = [v first, v second])
    (captured : arguments.map (applySubst bindings) = [left, right])
    (computed : PureReturns program (binaryEnvironment first second left right) state (rawEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head arguments) state answer :=
  raw_call helper bindings (binaryEnvironment first second left right) state arguments [left, right] answer
    (by simp [arity]) captured (binary_clause helper first second left right different formals) computed

private theorem cons_template_named (first second : String) :
    PureData.Template program (a "LCons" [v first, v second]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private def commonPrefixCons : Atom :=
  a "if" [a "==" [v "first", v "actual"],
    a "let" [v "tail", a "gslt:normalized:common-prefix" [v "left-rest", v "right-rest"],
      a "LCons" [v "first", v "tail"]], .symbol "LNil"]

private def commonPrefixCases : SpaceSemantics.Cases :=
  [(.expression [a "LCons" [v "first", v "left-rest"], a "LCons" [v "actual", v "right-rest"]], commonPrefixCons),
   (v "bad", .symbol "LNil")]

private theorem commonPrefix_shape : (rawEquation .commonPrefix).body =
    a "case" [.expression [v "left", v "right"],
      .expression (commonPrefixCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem commonPrefix_call (bindings : Subst) (state : State) (left right : Position)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm left), encoded (positionTerm right)])
    (computed : PureReturns program
      (binaryEnvironment "left" "right" (encoded (positionTerm left)) (encoded (positionTerm right))) state
      (rawEquation .commonPrefix).body state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.commonPrefix left right)))) :
    PureReturns program bindings state (a "gslt:normalized:common-prefix" arguments) state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.commonPrefix left right))) :=
  binary_call .commonPrefix "left" "right" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem commonPrefix_body_returns (state : State) (left right : Position) :
    PureReturns program
      (binaryEnvironment "left" "right" (encoded (positionTerm left)) (encoded (positionTerm right))) state
      (rawEquation .commonPrefix).body state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.commonPrefix left right))) := by
  induction left generalizing right with
  | nil =>
      let bindings := binaryEnvironment "left" "right" (encoded (positionTerm [])) (encoded (positionTerm right))
      let pair : Atom := .expression [encoded (positionTerm []), encoded (positionTerm right)]
      let selected := ("bad", pair) :: bindings
      rw [commonPrefix_shape]
      apply case_returns program bindings selected state state state (.expression [v "left", v "right"])
        pair (.symbol "LNil") _ _ commonPrefixCases (read_cases_encoded _) _ _ _
      · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
      · simp [commonPrefixCases, pair, positionTerm, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · exact symbol_returns program selected state "LNil"
  | cons first rest ih =>
      cases right with
      | nil =>
          let bindings := binaryEnvironment "left" "right" (encoded (positionTerm (first :: rest))) (encoded (positionTerm []))
          let pair : Atom := .expression [encoded (positionTerm (first :: rest)), encoded (positionTerm [])]
          let selected := ("bad", pair) :: bindings
          rw [commonPrefix_shape]
          apply case_returns program bindings selected state state state (.expression [v "left", v "right"])
            pair (.symbol "LNil") _ _ commonPrefixCases (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
          · simp [commonPrefixCases, pair, positionTerm, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
          · exact symbol_returns program selected state "LNil"
      | cons actual right =>
          let bindings := binaryEnvironment "left" "right" (encoded (positionTerm (first :: rest)))
            (encoded (positionTerm (actual :: right)))
          let pair : Atom := .expression [encoded (positionTerm (first :: rest)), encoded (positionTerm (actual :: right))]
          let selected := ("right-rest", encoded (positionTerm right)) :: ("actual", number actual) ::
            ("left-rest", encoded (positionTerm rest)) :: ("first", number first) :: bindings
          rw [commonPrefix_shape]
          apply case_returns program bindings selected state state state (.expression [v "left", v "right"])
            pair commonPrefixCons _ _ commonPrefixCases (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
          · simp [commonPrefixCases, pair, positionTerm, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
          · have compared := CettaWireAtom.equality_captured_returns program selected state
              (.natural first) (.natural actual) "first" "actual"
              (by simp [selected, applySubst, Subst.lookup])
              (by simp [selected, applySubst, Subst.lookup])
            apply if_returns program selected state state state _ _ _ _ _ compared
            by_cases same : first = actual
            · subst actual
              let tail := encoded (positionTerm (TopDownMatchDerivativeNormalization.commonPrefix rest right))
              let bound := ("tail", tail) :: selected
              simp only [decide_true, BEq.rfl, ite_true]
              apply let_returns program selected bound state state state (v "tail")
                (a "gslt:normalized:common-prefix" [v "left-rest", v "right-rest"])
                (a "LCons" [v "first", v "tail"]) tail _
              · exact commonPrefix_call selected state rest right _
                  (by simp [selected, applySubst, Subst.lookup]) (ih right)
              · simp [bound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup]
              · simpa [TopDownMatchDerivativeNormalization.commonPrefix, tail, bound, selected,
                  positionTerm, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program bound state _ (cons_template_named "first" "tail")
            · simpa [Term.natural.injEq, same, Effects.boolean,
                TopDownMatchDerivativeNormalization.commonPrefix, positionTerm, encodeList, CettaWireAtom.encode] using
                symbol_returns program selected state "LNil"

theorem commonPrefix_captured_returns (bindings : Subst) (state : State) (left right : Position)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm left), encoded (positionTerm right)]) :
    PureReturns program bindings state (a "gslt:normalized:common-prefix" arguments) state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.commonPrefix left right))) :=
  commonPrefix_call bindings state left right arguments captured (commonPrefix_body_returns state left right)

private def gcpCons : Atom :=
  a "let" [v "tail", a "gslt:normalized:gcp" [v "rest"],
    a "gslt:normalized:common-prefix" [v "first", v "tail"]]

private def gcpCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "first", .symbol "LNil"], v "first"),
   (a "LCons" [v "first", v "rest"], gcpCons)]

private theorem gcp_shape : (rawEquation .gcp).body =
    a "case" [v "positions", .expression (gcpCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem gcp_call (bindings : Subst) (state : State) (paths : List Position) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList positionTerm paths))
    (computed : PureReturns program (unaryEnvironment "positions" (encoded (encodeList positionTerm paths)))
      state (rawEquation .gcp).body state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.greatestCommonPrefix paths)))) :
    PureReturns program bindings state (a "gslt:normalized:gcp" [argument]) state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.greatestCommonPrefix paths))) :=
  unary_call .gcp "positions" bindings state argument _ _ rfl (by decide +kernel) captured computed

private theorem gcp_body_returns (state : State) (paths : List Position) :
    PureReturns program (unaryEnvironment "positions" (encoded (encodeList positionTerm paths)))
      state (rawEquation .gcp).body state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.greatestCommonPrefix paths))) := by
  induction paths with
  | nil =>
      let bindings := unaryEnvironment "positions" (encoded (encodeList positionTerm []))
      rw [gcp_shape]
      apply case_returns program bindings bindings state state state (v "positions") (.symbol "LNil")
        (.symbol "LNil") _ _ gcpCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "positions"
      · simp [gcpCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := unaryEnvironment "positions" (encoded (encodeList positionTerm (first :: rest)))
      rw [gcp_shape]
      cases rest with
      | nil =>
          let selected := ("first", encoded (positionTerm first)) :: bindings
          apply case_returns program bindings selected state state state (v "positions")
            (encoded (encodeList positionTerm [first])) (v "first") _ _ gcpCases
            (read_cases_encoded _) _ _ _
          · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using
              variable_returns program bindings state "positions"
          · simp [gcpCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
          · simpa [selected, applySubst, Subst.lookup,
              TopDownMatchDerivativeNormalization.greatestCommonPrefix] using
              variable_returns program selected state "first"
      | cons next rest =>
          let selected := ("rest", encoded (encodeList positionTerm (next :: rest))) ::
            ("first", encoded (positionTerm first)) :: bindings
          let tail := encoded (positionTerm (TopDownMatchDerivativeNormalization.greatestCommonPrefix (next :: rest)))
          let bound := ("tail", tail) :: selected
          apply case_returns program bindings selected state state state (v "positions")
            (encoded (encodeList positionTerm (first :: next :: rest))) gcpCons _ _ gcpCases
            (read_cases_encoded _) _ _ _
          · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using
              variable_returns program bindings state "positions"
          · simp [gcpCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
          · apply let_returns program selected bound state state state (v "tail")
              (a "gslt:normalized:gcp" [v "rest"])
              (a "gslt:normalized:common-prefix" [v "first", v "tail"]) tail _
            · exact gcp_call selected state (next :: rest) (v "rest")
                (by simp [selected, applySubst, Subst.lookup]) ih
            · simp [bound, selected, bindings, unaryEnvironment, SpaceSemantics.matchBinding,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact commonPrefix_captured_returns bound state first
                (TopDownMatchDerivativeNormalization.greatestCommonPrefix (next :: rest)) _
                (by simp [bound, tail, selected, applySubst, Subst.lookup])

theorem gcp_captured_returns (bindings : Subst) (state : State) (paths : List Position) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList positionTerm paths)) :
    PureReturns program bindings state (a "gslt:normalized:gcp" [argument]) state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.greatestCommonPrefix paths))) :=
  gcp_call bindings state paths argument captured (gcp_body_returns state paths)

private def dropCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", v "whole"], v "whole"),
   (.expression [a "LCons" [v "ignored-base", v "base-rest"], a "LCons" [v "ignored-path", v "path-rest"]],
     a "gslt:normalized:drop-displacement" [v "base-rest", v "path-rest"]),
   (v "bad", .symbol "LNil")]

private theorem drop_shape : (rawEquation .dropDisplacement).body =
    a "case" [.expression [v "base", v "path"],
      .expression (dropCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem drop_call (bindings : Subst) (state : State) (base path : Position)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (positionTerm path)])
    (computed : PureReturns program
      (binaryEnvironment "base" "path" (encoded (positionTerm base)) (encoded (positionTerm path))) state
      (rawEquation .dropDisplacement).body state (encoded (positionTerm (path.drop base.length)))) :
    PureReturns program bindings state (a "gslt:normalized:drop-displacement" arguments) state
      (encoded (positionTerm (path.drop base.length))) :=
  binary_call .dropDisplacement "base" "path" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem drop_body_returns (state : State) (base path : Position) :
    PureReturns program
      (binaryEnvironment "base" "path" (encoded (positionTerm base)) (encoded (positionTerm path))) state
      (rawEquation .dropDisplacement).body state (encoded (positionTerm (path.drop base.length))) := by
  induction base generalizing path with
  | nil =>
      let bindings := binaryEnvironment "base" "path" (encoded (positionTerm [])) (encoded (positionTerm path))
      let selected := ("whole", encoded (positionTerm path)) :: bindings
      rw [drop_shape]
      apply case_returns program bindings selected state state state (.expression [v "base", v "path"])
        (.expression [encoded (positionTerm []), encoded (positionTerm path)]) (v "whole") _ _ dropCases
        (read_cases_encoded _) _ _ _
      · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
      · simp [dropCases, positionTerm, encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · simpa [selected, applySubst, Subst.lookup] using variable_returns program selected state "whole"
  | cons ignored base ih =>
      cases path with
      | nil =>
          let bindings := binaryEnvironment "base" "path" (encoded (positionTerm (ignored :: base))) (encoded (positionTerm []))
          let pair : Atom := .expression [encoded (positionTerm (ignored :: base)), encoded (positionTerm [])]
          let selected := ("bad", pair) :: bindings
          rw [drop_shape]
          apply case_returns program bindings selected state state state (.expression [v "base", v "path"])
            pair (.symbol "LNil") _ _ dropCases (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
          · simp [dropCases, pair, positionTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
          · exact symbol_returns program selected state "LNil"
      | cons actual path =>
          let bindings := binaryEnvironment "base" "path" (encoded (positionTerm (ignored :: base)))
            (encoded (positionTerm (actual :: path)))
          let pair : Atom := .expression [encoded (positionTerm (ignored :: base)), encoded (positionTerm (actual :: path))]
          let selected := ("path-rest", encoded (positionTerm path)) :: ("ignored-path", number actual) ::
            ("base-rest", encoded (positionTerm base)) :: ("ignored-base", number ignored) :: bindings
          rw [drop_shape]
          apply case_returns program bindings selected state state state (.expression [v "base", v "path"])
            pair (a "gslt:normalized:drop-displacement" [v "base-rest", v "path-rest"]) _ _ dropCases
            (read_cases_encoded _) _ _ _
          · apply variable_pair_returns <;> simp [bindings, binaryEnvironment, applySubst, Subst.lookup]
          · simp [dropCases, pair, positionTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
          · simpa only [List.length_cons, List.drop_succ_cons] using
              drop_call selected state base path [v "base-rest", v "path-rest"]
                (by simp [selected, applySubst, Subst.lookup]) (ih path)

theorem drop_captured_returns (bindings : Subst) (state : State) (base path : Position)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (positionTerm path)]) :
    PureReturns program bindings state (a "gslt:normalized:drop-displacement" arguments) state
      (encoded (positionTerm (path.drop base.length))) :=
  drop_call bindings state base path arguments captured (drop_body_returns state base path)

private def relativePendingCons : Atom :=
  a "let*" [.expression [.expression [v "relative", a "gslt:normalized:drop-displacement" [v "base", v "position"]],
    .expression [v "tail", a "gslt:normalized:relative-pending" [v "base", v "rest"]]],
    a "LCons" [a "Observe" [v "relative", v "key"], v "tail"]]

private def relativePendingCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "Observe" [v "position", v "key"], v "rest"], relativePendingCons)]

private theorem relativePending_shape : (rawEquation .relativePending).body =
    a "case" [v "pending", .expression (relativePendingCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem relativePending_template :
    PureData.Template program (a "LCons" [a "Observe" [v "relative", v "key"], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Observe" _ (by decide +kernel) (by decide)
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

private theorem relativePending_call (bindings : Subst) (state : State) (base : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (encodeList obligationTerm pending)])
    (computed : PureReturns program
      (binaryEnvironment "base" "pending" (encoded (positionTerm base)) (encoded (encodeList obligationTerm pending)))
      state (rawEquation .relativePending).body state
      (encoded (encodeList obligationTerm (pending.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩)))) :
    PureReturns program bindings state (a "gslt:normalized:relative-pending" arguments) state
      (encoded (encodeList obligationTerm (pending.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩))) :=
  binary_call .relativePending "base" "pending" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem relativePending_body_returns (state : State) (base : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program
      (binaryEnvironment "base" "pending" (encoded (positionTerm base)) (encoded (encodeList obligationTerm pending)))
      state (rawEquation .relativePending).body state
      (encoded (encodeList obligationTerm (pending.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩))) := by
  induction pending with
  | nil =>
      let bindings := binaryEnvironment "base" "pending" (encoded (positionTerm base)) (encoded (encodeList obligationTerm []))
      rw [relativePending_shape]
      apply case_returns program bindings bindings state state state (v "pending") (.symbol "LNil")
        (.symbol "LNil") _ _ relativePendingCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [relativePendingCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := binaryEnvironment "base" "pending" (encoded (positionTerm base))
        (encoded (encodeList obligationTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList obligationTerm rest)) :: ("key", encoded (keyTerm first.key)) ::
        ("position", encoded (positionTerm first.position)) :: bindings
      let relativeBound := ("relative", encoded (positionTerm (first.position.drop base.length))) :: selected
      let tail := encoded (encodeList obligationTerm (rest.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩))
      let tailBound := ("tail", tail) :: relativeBound
      rw [relativePending_shape]
      apply case_returns program bindings selected state state state (v "pending")
        (encoded (encodeList obligationTerm (first :: rest))) relativePendingCons _ _ relativePendingCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [relativePendingCases, encodeList, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply PureData.let_bindings_return
          (program := program) (bindings := selected) (before := state) (middle := state)
          (pairs := [(v "relative", a "gslt:normalized:drop-displacement" [v "base", v "position"]),
            (v "tail", a "gslt:normalized:relative-pending" [v "base", v "rest"])])
          (final := tailBound) _ state (a "LCons" [a "Observe" [v "relative", v "key"], v "tail"]) _ _
        · apply PureData.BindingsReturn.cons (bound := relativeBound)
            (value := encoded (positionTerm (first.position.drop base.length)))
          · exact drop_captured_returns selected state base first.position _
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              relativeBound, selected, bindings, binaryEnvironment]
          · apply PureData.BindingsReturn.cons (bound := tailBound) (value := tail)
            · exact relativePending_call relativeBound state base rest _
                (by simp [relativeBound, selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                tailBound, relativeBound, selected, bindings, binaryEnvironment]
            · exact .nil _ _
        · simpa [tailBound, tail, relativeBound, selected, encodeList, obligationTerm, applySubst,
            applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program tailBound state _ relativePending_template

theorem relativePending_captured_returns (bindings : Subst) (state : State) (base : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (encodeList obligationTerm pending)]) :
    PureReturns program bindings state (a "gslt:normalized:relative-pending" arguments) state
      (encoded (encodeList obligationTerm (pending.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩))) :=
  relativePending_call bindings state base pending arguments captured (relativePending_body_returns state base pending)

private def indexCons : Atom :=
  a "if" [a "==" [v "value", v "first"], number 0,
    a "let" [v "tail", a "gslt:normalized:index" [v "value", v "rest"], a "+" [number 1, v "tail"]]]

private def indexCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", number 0), (a "LCons" [v "first", v "rest"], indexCons)]

private theorem index_shape : (rawEquation .index).body =
    a "case" [v "values", .expression (indexCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem index_call (bindings : Subst) (state : State) (value : Term) (values : List Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) = [encoded value, listValue values])
    (computed : PureReturns program (binaryEnvironment "value" "values" (encoded value) (listValue values))
      state (rawEquation .index).body state (number (values.idxOf value))) :
    PureReturns program bindings state (a "gslt:normalized:index" arguments) state (number (values.idxOf value)) :=
  binary_call .index "value" "values" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem index_body_returns (state : State) (value : Term) (values : List Term) :
    PureReturns program (binaryEnvironment "value" "values" (encoded value) (listValue values))
      state (rawEquation .index).body state (number (values.idxOf value)) := by
  induction values with
  | nil =>
      let bindings := binaryEnvironment "value" "values" (encoded value) (listValue [])
      rw [index_shape]
      apply case_returns program bindings bindings state state state (v "values") (.symbol "LNil")
        (number 0) _ _ indexCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "values"
      · simp [indexCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.int 0)
  | cons first rest ih =>
      let bindings := binaryEnvironment "value" "values" (encoded value) (listValue (first :: rest))
      let selected := ("rest", listValue rest) :: ("first", encoded first) :: bindings
      rw [index_shape]
      apply case_returns program bindings selected state state state (v "values") (listValue (first :: rest))
        indexCons _ _ indexCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "values"
      · simp [indexCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · have compared := CettaWireAtom.equality_captured_returns program selected state value first "value" "first"
          (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
          (by simp [selected, applySubst, Subst.lookup])
        apply if_returns program selected state state state _ _ _ _ _ compared
        by_cases same : value = first
        · subst first
          simpa [List.idxOf_cons, Effects.boolean, CettaWireAtom.encode] using
            grounded_returns program selected state (.int 0)
        · let tailBound := ("tail", number (rest.idxOf value)) :: selected
          simp only [same, decide_false, Effects.boolean]
          apply let_returns program selected tailBound state state state (v "tail")
            (a "gslt:normalized:index" [v "value", v "rest"]) (a "+" [number 1, v "tail"])
            (number (rest.idxOf value)) _
          · exact index_call selected state value rest _
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              tailBound, selected, bindings, binaryEnvironment]
          · have sum : PureReturns program tailBound state (a "+" [number 1, v "tail"])
                state (number (1 + rest.idxOf value)) := by
              apply native_binary_call_returns program tailBound state state state state "+"
                (number 1) (v "tail") (number 1) (number (rest.idxOf value)) (number (1 + rest.idxOf value))
                (by decide) (by decide) (by decide +kernel) (by decide +kernel)
              · exact grounded_returns program tailBound state (.int 1)
              · simpa [tailBound, applySubst, Subst.lookup] using variable_returns program tailBound state "tail"
              · change (Except.ok (state, [Atom.grounded (.int (1 + (rest.idxOf value : Int)))]) :
                    Except Effects.Fault (State × List Atom)) =
                  .ok (state, [Atom.grounded (.int ((1 + rest.idxOf value : Nat) : Int))])
                simp
              · decide
            simpa [List.idxOf_cons, Ne.symm same, Nat.add_comm] using sum

theorem index_captured_returns (bindings : Subst) (state : State) (value : Term) (values : List Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) = [encoded value, listValue values]) :
    PureReturns program bindings state (a "gslt:normalized:index" arguments) state (number (values.idxOf value)) :=
  index_call bindings state value values arguments captured (index_body_returns state value values)

private theorem goal_template_named (position occurrence pending : String) :
    PureData.Template program (a "MGoal" [a "At" [v position, v occurrence], v pending]) := by
  apply PureData.Template.constructor "MGoal" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "At" _ (by decide +kernel) (by decide)
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

private def rebaseEnvironment (base : Position) (goal : TopDownMatchDerivatives.Goal Term) : Subst :=
  [("pending", encoded (encodeList obligationTerm goal.pending)), ("occurrence", number goal.location.occurrence),
   ("position", encoded (positionTerm goal.location.position)), ("base", encoded (positionTerm base))]

private theorem rebase_clause (base : Position) (goal : TopDownMatchDerivatives.Goal Term) :
    clauses program "gslt:normalized:rebase" [encoded (positionTerm base), encoded (goalTerm goal)] =
      [.evaluate (rebaseEnvironment base goal) (rawEquation .rebase).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:rebase").filterMap _ = _
  rw [show equations "gslt:normalized:rebase" = [rawEquation .rebase] from rfl]
  have formals : (rawEquation .rebase).arguments =
      [v "base", a "MGoal" [a "At" [v "position", v "occurrence"], v "pending"]] := by decide +kernel
  simp [formals, goalTerm, locationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
    rebaseEnvironment]

private def rebasePairs : List (Atom × Atom) :=
  [(v "relative", a "gslt:normalized:drop-displacement" [v "base", v "position"]),
   (v "residual", a "gslt:normalized:relative-pending" [v "base", v "pending"])]

private def rebaseResult : Atom := a "MGoal" [a "At" [v "relative", v "occurrence"], v "residual"]

private theorem rebase_shape : (rawEquation .rebase).body =
    a "let*" [.expression (rebasePairs.map fun row => .expression [row.1, row.2]), rebaseResult] := by
  decide +kernel

theorem rebase_captured_returns (bindings : Subst) (state : State) (base : Position)
    (goal : TopDownMatchDerivatives.Goal Term) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm base), encoded (goalTerm goal)]) :
    PureReturns program bindings state (a "gslt:normalized:rebase" arguments) state
      (encoded (goalTerm (TopDownMatchDerivativeNormalization.relativize base goal))) := by
  apply raw_call .rebase bindings (rebaseEnvironment base goal) state arguments _ _ rfl captured (rebase_clause base goal)
  let callee := rebaseEnvironment base goal
  let relative := encoded (positionTerm (goal.location.position.drop base.length))
  let relativeBound := ("relative", relative) :: callee
  let residual := encoded (encodeList obligationTerm (goal.pending.map fun obligation =>
    ⟨obligation.position.drop base.length, obligation.key⟩))
  let residualBound := ("residual", residual) :: relativeBound
  rw [rebase_shape]
  apply PureData.let_bindings_return (program := program) (bindings := callee)
    (before := state) (middle := state) (pairs := rebasePairs) (final := residualBound)
    _ state rebaseResult _ _
  · apply PureData.BindingsReturn.cons (bound := relativeBound) (value := relative)
    · exact drop_captured_returns callee state base goal.location.position _
        (by simp [callee, rebaseEnvironment, applySubst, Subst.lookup])
    · simp [relativeBound, callee, rebaseEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := residualBound) (value := residual)
      · exact relativePending_captured_returns relativeBound state base goal.pending _
          (by simp [relativeBound, callee, rebaseEnvironment, applySubst, Subst.lookup])
      · simp [residualBound, relativeBound, callee, rebaseEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · exact .nil _ _
  · simpa [rebaseResult, TopDownMatchDerivativeNormalization.relativize, goalTerm, locationTerm,
      residualBound, residual, relativeBound, relative, callee, rebaseEnvironment, applySubst,
      applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program residualBound state _ (goal_template_named "relative" "occurrence" "residual")

private def pendingPositionsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "Observe" [v "position", v "key"], v "rest"],
    a "let" [v "tail", a "gslt:normalized:pending-positions" [v "rest"], a "LCons" [v "position", v "tail"]])]

private theorem pendingPositions_shape : (rawEquation .pendingPositions).body =
    a "case" [v "pending", .expression (pendingPositionsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem pendingPositions_call (bindings : Subst) (state : State)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList obligationTerm pending))
    (computed : PureReturns program (unaryEnvironment "pending" (encoded (encodeList obligationTerm pending)))
      state (rawEquation .pendingPositions).body state
      (encoded (encodeList positionTerm (pending.map (·.position))))) :
    PureReturns program bindings state (a "gslt:normalized:pending-positions" [argument]) state
      (encoded (encodeList positionTerm (pending.map (·.position)))) :=
  unary_call .pendingPositions "pending" bindings state argument _ _ rfl (by decide +kernel) captured computed

private theorem pendingPositions_body_returns (state : State)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program (unaryEnvironment "pending" (encoded (encodeList obligationTerm pending)))
      state (rawEquation .pendingPositions).body state
      (encoded (encodeList positionTerm (pending.map (·.position)))) := by
  induction pending with
  | nil =>
      let bindings := unaryEnvironment "pending" (encoded (encodeList obligationTerm []))
      rw [pendingPositions_shape]
      apply case_returns program bindings bindings state state state (v "pending") (.symbol "LNil")
        (.symbol "LNil") _ _ pendingPositionsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [pendingPositionsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := unaryEnvironment "pending" (encoded (encodeList obligationTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList obligationTerm rest)) :: ("key", encoded (keyTerm first.key)) ::
        ("position", encoded (positionTerm first.position)) :: bindings
      let tail := encoded (encodeList positionTerm (rest.map (·.position)))
      let bound := ("tail", tail) :: selected
      rw [pendingPositions_shape]
      apply case_returns program bindings selected state state state (v "pending")
        (encoded (encodeList obligationTerm (first :: rest)))
        (a "let" [v "tail", a "gslt:normalized:pending-positions" [v "rest"], a "LCons" [v "position", v "tail"]])
        _ _ pendingPositionsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [pendingPositionsCases, encodeList, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
      · apply let_returns program selected bound state state state (v "tail")
          (a "gslt:normalized:pending-positions" [v "rest"]) (a "LCons" [v "position", v "tail"]) tail _
        · exact pendingPositions_call selected state rest (v "rest")
            (by simp [selected, applySubst, Subst.lookup]) ih
        · simp [bound, selected, bindings, unaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · simpa [bound, tail, selected, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program bound state _ (cons_template_named "position" "tail")

theorem pendingPositions_captured_returns (bindings : Subst) (state : State)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList obligationTerm pending)) :
    PureReturns program bindings state (a "gslt:normalized:pending-positions" [argument]) state
      (encoded (encodeList positionTerm (pending.map (·.position)))) :=
  pendingPositions_call bindings state pending argument captured (pendingPositions_body_returns state pending)

private def positionsCons : Atom :=
  a "let*" [.expression [.expression [v "here", a "gslt:normalized:pending-positions" [v "pending"]],
    .expression [v "below", a "gslt:normalized:positions" [v "rest"]],
    .expression [v "all", a "gslt:automata:append" [v "here", v "below"]]],
    a "LCons" [v "position", v "all"]]

private def positionsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "MGoal" [a "At" [v "position", v "occurrence"], v "pending"], v "rest"], positionsCons)]

private theorem positions_shape : (rawEquation .positions).body =
    a "case" [v "component", .expression (positionsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem positions_call (bindings : Subst) (state : State)
    (component : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm component))
    (computed : PureReturns program (unaryEnvironment "component" (encoded (encodeList goalTerm component)))
      state (rawEquation .positions).body state
      (encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions component)))) :
    PureReturns program bindings state (a "gslt:normalized:positions" [argument]) state
      (encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions component))) :=
  unary_call .positions "component" bindings state argument _ _ rfl (by decide +kernel) captured computed

private theorem positions_body_returns (state : State)
    (component : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program (unaryEnvironment "component" (encoded (encodeList goalTerm component)))
      state (rawEquation .positions).body state
      (encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions component))) := by
  induction component with
  | nil =>
      let bindings := unaryEnvironment "component" (encoded (encodeList goalTerm []))
      rw [positions_shape]
      apply case_returns program bindings bindings state state state (v "component") (.symbol "LNil")
        (.symbol "LNil") _ _ positionsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "component"
      · simp [positionsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := unaryEnvironment "component" (encoded (encodeList goalTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList goalTerm rest)) :: ("pending", encoded (encodeList obligationTerm first.pending)) ::
        ("occurrence", number first.location.occurrence) :: ("position", encoded (positionTerm first.location.position)) :: bindings
      let here := encoded (encodeList positionTerm (first.pending.map (·.position)))
      let hereBound := ("here", here) :: selected
      let below := encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions rest))
      let belowBound := ("below", below) :: hereBound
      let all := encoded (encodeList positionTerm (first.pending.map (·.position) ++
        TopDownMatchDerivativeNormalization.componentPositions rest))
      let allBound := ("all", all) :: belowBound
      rw [positions_shape]
      apply case_returns program bindings selected state state state (v "component")
        (encoded (encodeList goalTerm (first :: rest))) positionsCons _ _ positionsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "component"
      · simp [positionsCases, encodeList, goalTerm, locationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
      · apply PureData.let_bindings_return
          (program := program) (bindings := selected) (before := state) (middle := state)
          (pairs := [(v "here", a "gslt:normalized:pending-positions" [v "pending"]),
            (v "below", a "gslt:normalized:positions" [v "rest"]),
            (v "all", a "gslt:automata:append" [v "here", v "below"])])
          (final := allBound) _ state (a "LCons" [v "position", v "all"]) _ _
        · apply PureData.BindingsReturn.cons (bound := hereBound) (value := here)
          · exact pendingPositions_captured_returns selected state first.pending (v "pending")
              (by simp [selected, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              hereBound, selected, bindings, unaryEnvironment]
          · apply PureData.BindingsReturn.cons (bound := belowBound) (value := below)
            · exact positions_call hereBound state rest (v "rest")
                (by simp [hereBound, selected, applySubst, Subst.lookup]) ih
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                belowBound, hereBound, selected, bindings, unaryEnvironment]
            · apply PureData.BindingsReturn.cons (bound := allBound) (value := all)
              · have old := MatchAutomataSourceExecution.append_captured_returns belowBound state
                  ((first.pending.map (·.position)).map positionTerm)
                  ((TopDownMatchDerivativeNormalization.componentPositions rest).map positionTerm)
                  (v "here") (v "below")
                  (by simp [belowBound, below, hereBound, here, applySubst, Subst.lookup, listValue, encodeList_map])
                simpa only [all, listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using
                  automata_captured_returns (by decide +kernel) old
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                  allBound, belowBound, hereBound, selected, bindings, unaryEnvironment]
              · exact .nil _ _
        · simpa [TopDownMatchDerivativeNormalization.componentPositions, allBound, all, belowBound,
            hereBound, selected, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program allBound state _ (cons_template_named "position" "all")

theorem positions_captured_returns (bindings : Subst) (state : State)
    (component : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm component)) :
    PureReturns program bindings state (a "gslt:normalized:positions" [argument]) state
      (encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions component))) :=
  positions_call bindings state component argument captured (positions_body_returns state component)

private theorem base_shape : (rawEquation .base).body =
    a "let" [v "positions", a "gslt:normalized:positions" [v "component"], a "gslt:normalized:gcp" [v "positions"]] := by
  decide +kernel

theorem base_captured_returns (bindings : Subst) (state : State)
    (component : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm component)) :
    PureReturns program bindings state (a "gslt:normalized:base" [argument]) state
      (encoded (positionTerm (TopDownMatchDerivativeNormalization.componentBase component))) := by
  apply unary_call .base "component" bindings state argument _ _ rfl (by decide +kernel) captured
  let callee := unaryEnvironment "component" (encoded (encodeList goalTerm component))
  let positions := encoded (encodeList positionTerm (TopDownMatchDerivativeNormalization.componentPositions component))
  let bound := ("positions", positions) :: callee
  rw [base_shape]
  apply let_returns program callee bound state state state (v "positions")
    (a "gslt:normalized:positions" [v "component"]) (a "gslt:normalized:gcp" [v "positions"]) positions _
  · exact positions_captured_returns callee state component (v "component")
      (by simp [callee, unaryEnvironment, applySubst, Subst.lookup])
  · simp [bound, callee, unaryEnvironment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup]
  · exact gcp_captured_returns bound state (TopDownMatchDerivativeNormalization.componentPositions component) (v "positions")
      (by simp [bound, positions, applySubst, Subst.lookup])

private theorem positionTerm_injective : Function.Injective positionTerm :=
  encodeList_injective Term.natural (fun _ _ same => Term.natural.inj same)

private def positionMemberCons : Atom :=
  a "if" [a "==" [v "position", v "other"], Effects.boolean true,
    a "gslt:normalized:position-member" [v "position", v "rest"]]

private def positionMemberCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false),
   (a "LCons" [a "Observe" [v "other", v "key"], v "rest"], positionMemberCons)]

private theorem positionMember_shape : (rawEquation .positionMember).body =
    a "case" [v "pending", .expression (positionMemberCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem positionMember_call (bindings : Subst) (state : State) (position : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm position), encoded (encodeList obligationTerm pending)])
    (computed : PureReturns program
      (binaryEnvironment "position" "pending" (encoded (positionTerm position)) (encoded (encodeList obligationTerm pending)))
      state (rawEquation .positionMember).body state
      (Effects.boolean (pending.any fun obligation => decide (position = obligation.position)))) :
    PureReturns program bindings state (a "gslt:normalized:position-member" arguments) state
      (Effects.boolean (pending.any fun obligation => decide (position = obligation.position))) :=
  binary_call .positionMember "position" "pending" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem positionMember_body_returns (state : State) (position : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program
      (binaryEnvironment "position" "pending" (encoded (positionTerm position)) (encoded (encodeList obligationTerm pending)))
      state (rawEquation .positionMember).body state
      (Effects.boolean (pending.any fun obligation => decide (position = obligation.position))) := by
  induction pending with
  | nil =>
      let bindings := binaryEnvironment "position" "pending" (encoded (positionTerm position)) (encoded (encodeList obligationTerm []))
      rw [positionMember_shape]
      apply case_returns program bindings bindings state state state (v "pending") (.symbol "LNil")
        (Effects.boolean false) _ _ positionMemberCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [positionMemberCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | cons first rest ih =>
      let bindings := binaryEnvironment "position" "pending" (encoded (positionTerm position))
        (encoded (encodeList obligationTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList obligationTerm rest)) :: ("key", encoded (keyTerm first.key)) ::
        ("other", encoded (positionTerm first.position)) :: bindings
      rw [positionMember_shape]
      apply case_returns program bindings selected state state state (v "pending")
        (encoded (encodeList obligationTerm (first :: rest))) positionMemberCons _ _ positionMemberCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "pending"
      · simp [positionMemberCases, encodeList, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · have compared := CettaWireAtom.equality_captured_returns program selected state
          (positionTerm position) (positionTerm first.position) "position" "other"
          (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
          (by simp [selected, applySubst, Subst.lookup])
        simp only [positionTerm_injective.eq_iff] at compared
        apply if_returns program selected state state state _ _ _ _ _ compared
        cases same : decide (position = first.position) with
        | false =>
            simpa [same, Effects.boolean] using
              positionMember_call selected state position rest _
                (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
        | true =>
            simpa [same, Effects.boolean] using grounded_returns program selected state (.bool true)

theorem positionMember_captured_returns (bindings : Subst) (state : State) (position : Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (positionTerm position), encoded (encodeList obligationTerm pending)]) :
    PureReturns program bindings state (a "gslt:normalized:position-member" arguments) state
      (Effects.boolean (pending.any fun obligation => decide (position = obligation.position))) :=
  positionMember_call bindings state position pending arguments captured (positionMember_body_returns state position pending)

private def overlapPendingCons : Atom :=
  a "if" [a "gslt:normalized:position-member" [v "position", v "right"], Effects.boolean true,
    a "gslt:normalized:overlap-pending" [v "rest", v "right"]]

private def overlapPendingCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false),
   (a "LCons" [a "Observe" [v "position", v "key"], v "rest"], overlapPendingCons)]

private theorem overlapPending_shape : (rawEquation .overlapPending).body =
    a "case" [v "left", .expression (overlapPendingCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem overlapPending_call (bindings : Subst) (state : State)
    (left right : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList obligationTerm left), encoded (encodeList obligationTerm right)])
    (computed : PureReturns program
      (binaryEnvironment "left" "right" (encoded (encodeList obligationTerm left)) (encoded (encodeList obligationTerm right)))
      state (rawEquation .overlapPending).body state
      (Effects.boolean (left.any fun first => right.any fun second => decide (first.position = second.position)))) :
    PureReturns program bindings state (a "gslt:normalized:overlap-pending" arguments) state
      (Effects.boolean (left.any fun first => right.any fun second => decide (first.position = second.position))) :=
  binary_call .overlapPending "left" "right" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem overlapPending_body_returns (state : State)
    (left right : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program
      (binaryEnvironment "left" "right" (encoded (encodeList obligationTerm left)) (encoded (encodeList obligationTerm right)))
      state (rawEquation .overlapPending).body state
      (Effects.boolean (left.any fun first => right.any fun second => decide (first.position = second.position))) := by
  induction left with
  | nil =>
      let bindings := binaryEnvironment "left" "right" (encoded (encodeList obligationTerm [])) (encoded (encodeList obligationTerm right))
      rw [overlapPending_shape]
      apply case_returns program bindings bindings state state state (v "left") (.symbol "LNil")
        (Effects.boolean false) _ _ overlapPendingCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "left"
      · simp [overlapPendingCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | cons first rest ih =>
      let bindings := binaryEnvironment "left" "right" (encoded (encodeList obligationTerm (first :: rest)))
        (encoded (encodeList obligationTerm right))
      let selected := ("rest", encoded (encodeList obligationTerm rest)) :: ("key", encoded (keyTerm first.key)) ::
        ("position", encoded (positionTerm first.position)) :: bindings
      rw [overlapPending_shape]
      apply case_returns program bindings selected state state state (v "left")
        (encoded (encodeList obligationTerm (first :: rest))) overlapPendingCons _ _ overlapPendingCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "left"
      · simp [overlapPendingCases, encodeList, obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply if_returns program selected state state state _ _ _ _ _
          (positionMember_captured_returns selected state first.position right _
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]))
        cases overlaps : right.any (fun second => decide (first.position = second.position)) with
        | false =>
            simpa [overlaps, Effects.boolean] using overlapPending_call selected state rest right _
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
        | true => simpa [overlaps, Effects.boolean] using grounded_returns program selected state (.bool true)

theorem overlapPending_captured_returns (bindings : Subst) (state : State)
    (left right : List (TopDownMatchDerivatives.Obligation Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList obligationTerm left), encoded (encodeList obligationTerm right)]) :
    PureReturns program bindings state (a "gslt:normalized:overlap-pending" arguments) state
      (Effects.boolean (left.any fun first => right.any fun second => decide (first.position = second.position))) :=
  overlapPending_call bindings state left right arguments captured (overlapPending_body_returns state left right)

private def overlapsEnvironment (first second : TopDownMatchDerivatives.Goal Term) : Subst :=
  [("right", encoded (encodeList obligationTerm second.pending)), ("second", encoded (locationTerm second.location)),
   ("left", encoded (encodeList obligationTerm first.pending)), ("first", encoded (locationTerm first.location))]

private theorem overlaps_clause (first second : TopDownMatchDerivatives.Goal Term) :
    clauses program "gslt:normalized:overlaps" [encoded (goalTerm first), encoded (goalTerm second)] =
      [.evaluate (overlapsEnvironment first second) (rawEquation .overlaps).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:overlaps").filterMap _ = _
  rw [show equations "gslt:normalized:overlaps" = [rawEquation .overlaps] from rfl]
  have formals : (rawEquation .overlaps).arguments =
      [a "MGoal" [v "first", v "left"], a "MGoal" [v "second", v "right"]] := by decide +kernel
  simp [formals, goalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, overlapsEnvironment]

theorem overlaps_captured_returns (bindings : Subst) (state : State)
    (first second : TopDownMatchDerivatives.Goal Term) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [encoded (goalTerm first), encoded (goalTerm second)]) :
    PureReturns program bindings state (a "gslt:normalized:overlaps" arguments) state
      (Effects.boolean (TopDownMatchDerivativeNormalization.overlaps first second)) := by
  apply raw_call .overlaps bindings (overlapsEnvironment first second) state arguments _ _ rfl captured (overlaps_clause first second)
  rw [show (rawEquation .overlaps).body = a "gslt:normalized:overlap-pending" [v "left", v "right"] by decide +kernel]
  exact overlapPending_captured_returns (overlapsEnvironment first second) state first.pending second.pending _
    (by simp [overlapsEnvironment, applySubst, Subst.lookup])

private def touchesCons : Atom :=
  a "if" [a "gslt:normalized:overlaps" [v "goal", v "first"], Effects.boolean true,
    a "gslt:normalized:touches" [v "goal", v "rest"]]

private def touchesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean false), (a "LCons" [v "first", v "rest"], touchesCons)]

private theorem touches_shape : (rawEquation .touches).body =
    a "case" [v "component", .expression (touchesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem touches_call (bindings : Subst) (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (component : List (TopDownMatchDerivatives.Goal Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [encoded (goalTerm goal), encoded (encodeList goalTerm component)])
    (computed : PureReturns program
      (binaryEnvironment "goal" "component" (encoded (goalTerm goal)) (encoded (encodeList goalTerm component)))
      state (rawEquation .touches).body state (Effects.boolean (TopDownMatchDerivativeNormalization.touches goal component))) :
    PureReturns program bindings state (a "gslt:normalized:touches" arguments) state
      (Effects.boolean (TopDownMatchDerivativeNormalization.touches goal component)) :=
  binary_call .touches "goal" "component" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem touches_body_returns (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (component : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program
      (binaryEnvironment "goal" "component" (encoded (goalTerm goal)) (encoded (encodeList goalTerm component)))
      state (rawEquation .touches).body state (Effects.boolean (TopDownMatchDerivativeNormalization.touches goal component)) := by
  induction component with
  | nil =>
      let bindings := binaryEnvironment "goal" "component" (encoded (goalTerm goal)) (encoded (encodeList goalTerm []))
      rw [touches_shape]
      apply case_returns program bindings bindings state state state (v "component") (.symbol "LNil")
        (Effects.boolean false) _ _ touchesCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "component"
      · simp [touchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | cons first rest ih =>
      let bindings := binaryEnvironment "goal" "component" (encoded (goalTerm goal)) (encoded (encodeList goalTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList goalTerm rest)) :: ("first", encoded (goalTerm first)) :: bindings
      rw [touches_shape]
      apply case_returns program bindings selected state state state (v "component")
        (encoded (encodeList goalTerm (first :: rest))) touchesCons _ _ touchesCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "component"
      · simp [touchesCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply if_returns program selected state state state _ _ _ _ _
          (overlaps_captured_returns selected state goal first _
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]))
        cases overlap : TopDownMatchDerivativeNormalization.overlaps goal first with
        | false =>
            simpa [TopDownMatchDerivativeNormalization.touches, overlap, Effects.boolean] using
              touches_call selected state goal rest _
                (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
        | true =>
            simpa [TopDownMatchDerivativeNormalization.touches, overlap, Effects.boolean] using
              grounded_returns program selected state (.bool true)

theorem touches_captured_returns (bindings : Subst) (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (component : List (TopDownMatchDerivatives.Goal Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) = [encoded (goalTerm goal), encoded (encodeList goalTerm component)]) :
    PureReturns program bindings state (a "gslt:normalized:touches" arguments) state
      (Effects.boolean (TopDownMatchDerivativeNormalization.touches goal component)) :=
  touches_call bindings state goal component arguments captured (touches_body_returns state goal component)

/-- Temporary pair returned by the authored overlap partition. Its two lists
are exactly the selected flattening and the stable complementary components. -/
def partitionTerm (goal : TopDownMatchDerivatives.Goal Term)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) : Term :=
  .application "MPartition"
    [encodeList goalTerm ((components.filter (TopDownMatchDerivativeNormalization.touches goal)).flatten),
     encodeList (encodeList goalTerm) (components.filter fun component => !TopDownMatchDerivativeNormalization.touches goal component)]

private def partitionJoined : Atom :=
  a "let" [v "all", a "gslt:automata:append" [v "first", v "joined"], a "MPartition" [v "all", v "independent"]]

private def partitionFinished : Atom :=
  a "if" [a "gslt:normalized:touches" [v "goal", v "first"], partitionJoined,
    a "MPartition" [v "joined", a "LCons" [v "first", v "independent"]]]

private def partitionResultCases : SpaceSemantics.Cases :=
  [(a "MPartition" [v "joined", v "independent"], partitionFinished)]

private def partitionCons : Atom :=
  a "case" [a "gslt:normalized:partition" [v "goal", v "rest"],
    .expression (partitionResultCases.map fun row => .expression [row.1, row.2])]

private def partitionCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "MPartition" [.symbol "LNil", .symbol "LNil"]),
   (a "LCons" [v "first", v "rest"], partitionCons)]

private theorem partition_shape : (rawEquation .partition).body =
    a "case" [v "components", .expression (partitionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem partition_call (bindings : Subst) (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (goalTerm goal), encoded (encodeList (encodeList goalTerm) components)])
    (computed : PureReturns program
      (binaryEnvironment "goal" "components" (encoded (goalTerm goal)) (encoded (encodeList (encodeList goalTerm) components)))
      state (rawEquation .partition).body state (encoded (partitionTerm goal components))) :
    PureReturns program bindings state (a "gslt:normalized:partition" arguments) state (encoded (partitionTerm goal components)) :=
  binary_call .partition "goal" "components" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem partition_pair_template (first second : String) :
    PureData.Template program (a "MPartition" [v first, v second]) := by
  apply PureData.Template.constructor "MPartition" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem partition_body_returns (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) :
    PureReturns program
      (binaryEnvironment "goal" "components" (encoded (goalTerm goal)) (encoded (encodeList (encodeList goalTerm) components)))
      state (rawEquation .partition).body state (encoded (partitionTerm goal components)) := by
  induction components with
  | nil =>
      let bindings := binaryEnvironment "goal" "components" (encoded (goalTerm goal)) (encoded (encodeList (encodeList goalTerm) []))
      rw [partition_shape]
      apply case_returns program bindings bindings state state state (v "components") (.symbol "LNil")
        (a "MPartition" [.symbol "LNil", .symbol "LNil"]) _ _ partitionCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "components"
      · simp [partitionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · apply PureData.template_return
        apply PureData.Template.constructor "MPartition" _ (by decide +kernel) (by decide)
        intro argument member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact .symbol _
  | cons first rest ih =>
      let bindings := binaryEnvironment "goal" "components" (encoded (goalTerm goal))
        (encoded (encodeList (encodeList goalTerm) (first :: rest)))
      let selected := ("rest", encoded (encodeList (encodeList goalTerm) rest)) ::
        ("first", encoded (encodeList goalTerm first)) :: bindings
      let joined := (rest.filter (TopDownMatchDerivativeNormalization.touches goal)).flatten
      let independent := rest.filter fun component => !TopDownMatchDerivativeNormalization.touches goal component
      let selectedResult := ("independent", encoded (encodeList (encodeList goalTerm) independent)) ::
        ("joined", encoded (encodeList goalTerm joined)) :: selected
      rw [partition_shape]
      apply case_returns program bindings selected state state state (v "components")
        (encoded (encodeList (encodeList goalTerm) (first :: rest))) partitionCons _ _ partitionCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "components"
      · simp [partitionCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply case_returns program selected selectedResult state state state
          (a "gslt:normalized:partition" [v "goal", v "rest"]) (encoded (partitionTerm goal rest))
          partitionFinished _ _ partitionResultCases (read_cases_encoded _) _ _ _
        · exact partition_call selected state goal rest _
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
        · simp [partitionResultCases, partitionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selectedResult, joined, independent, selected, bindings, binaryEnvironment]
        · apply if_returns program selectedResult state state state _ _ _ _ _
            (touches_captured_returns selectedResult state goal first _
              (by simp [selectedResult, selected, bindings, binaryEnvironment, applySubst, Subst.lookup]))
          cases touching : TopDownMatchDerivativeNormalization.touches goal first with
          | false =>
              have template : PureData.Template program (a "MPartition" [v "joined", a "LCons" [v "first", v "independent"]]) := by
                apply PureData.Template.constructor "MPartition" _ (by decide +kernel) (by decide)
                intro argument member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl
                · exact .captured _
                · exact cons_template_named "first" "independent"
              simpa [touching, Effects.boolean, partitionTerm, joined, independent, selectedResult, selected,
                bindings, binaryEnvironment, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                PureData.template_return program selectedResult state _ template
          | true =>
              let all := encoded (encodeList goalTerm (first ++ joined))
              let bound := ("all", all) :: selectedResult
              simp only [Effects.boolean, BEq.rfl, ite_true]
              apply let_returns program selectedResult bound state state state (v "all")
                (a "gslt:automata:append" [v "first", v "joined"]) (a "MPartition" [v "all", v "independent"]) all _
              · have old := MatchAutomataSourceExecution.append_captured_returns selectedResult state
                  (first.map goalTerm) (joined.map goalTerm) (v "first") (v "joined")
                  (by simp [selectedResult, selected, applySubst, Subst.lookup, listValue, encodeList_map])
                simpa only [all, listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using
                  automata_captured_returns (by decide +kernel) old
              · simp [bound, selectedResult, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup]
              · simpa [touching, partitionTerm, all, bound, joined, independent, selectedResult, selected,
                  bindings, binaryEnvironment, applySubst, applySubst.applySubstList, Subst.lookup,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program bound state _ (partition_pair_template "all" "independent")

theorem partition_captured_returns (bindings : Subst) (state : State) (goal : TopDownMatchDerivatives.Goal Term)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (goalTerm goal), encoded (encodeList (encodeList goalTerm) components)]) :
    PureReturns program bindings state (a "gslt:normalized:partition" arguments) state (encoded (partitionTerm goal components)) :=
  partition_call bindings state goal components arguments captured (partition_body_returns state goal components)

private def componentsFinished : Atom := a "LCons" [a "LCons" [v "first", v "joined"], v "independent"]

private def componentsResultCases : SpaceSemantics.Cases :=
  [(a "MPartition" [v "joined", v "independent"], componentsFinished)]

private def componentsCons : Atom :=
  a "let" [v "previous", a "gslt:normalized:components" [v "rest"],
    a "case" [a "gslt:normalized:partition" [v "first", v "previous"],
      .expression (componentsResultCases.map fun row => .expression [row.1, row.2])]]

private def componentsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "first", v "rest"], componentsCons)]

private theorem components_shape : (rawEquation .components).body =
    a "case" [v "goals", .expression (componentsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem components_call (bindings : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm goals))
    (computed : PureReturns program (unaryEnvironment "goals" (encoded (encodeList goalTerm goals)))
      state (rawEquation .components).body state
      (encoded (encodeList (encodeList goalTerm) (TopDownMatchDerivativeNormalization.dependencyComponents goals)))) :
    PureReturns program bindings state (a "gslt:normalized:components" [argument]) state
      (encoded (encodeList (encodeList goalTerm) (TopDownMatchDerivativeNormalization.dependencyComponents goals))) :=
  unary_call .components "goals" bindings state argument _ _ rfl (by decide +kernel) captured computed

private theorem components_body_returns (state : State) (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program (unaryEnvironment "goals" (encoded (encodeList goalTerm goals)))
      state (rawEquation .components).body state
      (encoded (encodeList (encodeList goalTerm) (TopDownMatchDerivativeNormalization.dependencyComponents goals))) := by
  induction goals with
  | nil =>
      let bindings := unaryEnvironment "goals" (encoded (encodeList goalTerm []))
      rw [components_shape]
      apply case_returns program bindings bindings state state state (v "goals") (.symbol "LNil")
        (.symbol "LNil") _ _ componentsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "goals"
      · simp [componentsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := unaryEnvironment "goals" (encoded (encodeList goalTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList goalTerm rest)) :: ("first", encoded (goalTerm first)) :: bindings
      let previous := TopDownMatchDerivativeNormalization.dependencyComponents rest
      let previousBound := ("previous", encoded (encodeList (encodeList goalTerm) previous)) :: selected
      let joined := (previous.filter (TopDownMatchDerivativeNormalization.touches first)).flatten
      let independent := previous.filter fun component => !TopDownMatchDerivativeNormalization.touches first component
      let selectedResult := ("independent", encoded (encodeList (encodeList goalTerm) independent)) ::
        ("joined", encoded (encodeList goalTerm joined)) :: previousBound
      rw [components_shape]
      apply case_returns program bindings selected state state state (v "goals") (encoded (encodeList goalTerm (first :: rest)))
        componentsCons _ _ componentsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "goals"
      · simp [componentsCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
      · apply let_returns program selected previousBound state state state (v "previous")
          (a "gslt:normalized:components" [v "rest"])
          (a "case" [a "gslt:normalized:partition" [v "first", v "previous"],
            .expression (componentsResultCases.map fun row => .expression [row.1, row.2])])
          (encoded (encodeList (encodeList goalTerm) previous)) _
        · exact components_call selected state rest (v "rest") (by simp [selected, applySubst, Subst.lookup]) ih
        · simp [previousBound, selected, bindings, unaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply case_returns program previousBound selectedResult state state state
            (a "gslt:normalized:partition" [v "first", v "previous"]) (encoded (partitionTerm first previous))
            componentsFinished _ _ componentsResultCases (read_cases_encoded _) _ _ _
          · exact partition_captured_returns previousBound state first previous _
              (by simp [previousBound, selected, applySubst, Subst.lookup])
          · simp [componentsResultCases, partitionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selectedResult, joined, independent, previousBound, selected, bindings, unaryEnvironment]
          · have template : PureData.Template program componentsFinished := by
              apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
              intro argument member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact cons_template_named "first" "joined"
              · exact .captured _
            simpa [componentsFinished, TopDownMatchDerivativeNormalization.dependencyComponents, selectedResult,
              joined, independent, previousBound, previous, selected, encodeList, applySubst,
              applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program selectedResult state _ template

theorem components_captured_returns (bindings : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm goals)) :
    PureReturns program bindings state (a "gslt:normalized:components" [argument]) state
      (encoded (encodeList (encodeList goalTerm) (TopDownMatchDerivativeNormalization.dependencyComponents goals))) :=
  components_call bindings state goals argument captured (components_body_returns state goals)

private theorem keyTerm_injective : Function.Injective keyTerm := by
  intro left right same
  obtain ⟨head, arity⟩ := left
  obtain ⟨other, count⟩ := right
  have arguments := (Term.application.inj same).2
  have heads := (List.cons.inj arguments).1
  have arities := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ ConstructorKey.mk heads (Term.natural.inj arities)

private theorem obligationTerm_injective : Function.Injective obligationTerm := by
  intro left right same
  obtain ⟨position, key⟩ := left
  obtain ⟨other, second⟩ := right
  have arguments := (Term.application.inj same).2
  have positions := (List.cons.inj arguments).1
  have keys := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ TopDownMatchDerivatives.Obligation.mk (positionTerm_injective positions) (keyTerm_injective keys)

private theorem locationTerm_injective : Function.Injective locationTerm := by
  intro left right same
  obtain ⟨position, occurrence⟩ := left
  obtain ⟨other, index⟩ := right
  have arguments := (Term.application.inj same).2
  have positions := (List.cons.inj arguments).1
  have indices := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ Location.mk (positionTerm_injective positions) (Term.natural.inj indices)

private theorem goalTerm_injective : Function.Injective goalTerm := by
  intro left right same
  obtain ⟨location, pending⟩ := left
  obtain ⟨other, residual⟩ := right
  have arguments := (Term.application.inj same).2
  have locations := (List.cons.inj arguments).1
  have vectors := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ TopDownMatchDerivatives.Goal.mk (locationTerm_injective locations)
    (encodeList_injective obligationTerm obligationTerm_injective vectors)

private theorem goalTerm_mem_map (goal : TopDownMatchDerivatives.Goal Term)
    (goals : List (TopDownMatchDerivatives.Goal Term)) :
    goalTerm goal ∈ goals.map goalTerm ↔ goal ∈ goals := by
  constructor
  · intro member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    exact (goalTerm_injective same) ▸ present
  · intro member
    exact List.mem_map.mpr ⟨goal, member, rfl⟩

private theorem member_goal_variables_returns (bindings : Subst) (state : State)
    (goal : TopDownMatchDerivatives.Goal Term) (goals : List (TopDownMatchDerivatives.Goal Term))
    (first second : String) (capturedFirst : applySubst bindings (v first) = encoded (goalTerm goal))
    (capturedSecond : applySubst bindings (v second) = encoded (encodeList goalTerm goals)) :
    PureReturns program bindings state (a "gslt:automata:member" [v first, v second]) state
      (Effects.boolean (decide (goal ∈ goals))) := by
  have old : PureReturns MatchAutomataProgram.program bindings state
      (a "gslt:automata:member" [v first, v second]) state
      (Effects.boolean (decide (goalTerm goal ∈ goals.map goalTerm))) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] bindings state state "gslt:automata:member"
      [encoded (goalTerm goal), listValue (goals.map goalTerm)] [v first, v second] _ (by decide +kernel) _ (by decide)
      _ (MatchAutomataSourceExecution.member_returns state (goalTerm goal) (goals.map goalTerm))
    · intro index bounded
      have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl <;> decide +kernel
    · simp [capturedFirst, capturedSecond, listValue, encodeList_map]
  simpa only [goalTerm_mem_map] using
    automata_captured_returns (by
      simp only [codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons, List.all_nil, Bool.and_true]
      decide +kernel) old

private def componentForCons : Atom :=
  a "if" [a "gslt:automata:member" [v "goal", v "first"], v "first",
    a "gslt:normalized:component-for" [v "rest", v "goal"]]

private def componentForCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [v "goal", .symbol "LNil"]),
   (a "LCons" [v "first", v "rest"], componentForCons)]

private theorem componentFor_shape : (rawEquation .componentFor).body =
    a "case" [v "components", .expression (componentForCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem componentFor_call (bindings : Subst) (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goal : TopDownMatchDerivatives.Goal Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList goalTerm) components), encoded (goalTerm goal)])
    (computed : PureReturns program
      (binaryEnvironment "components" "goal" (encoded (encodeList (encodeList goalTerm) components)) (encoded (goalTerm goal)))
      state (rawEquation .componentFor).body state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.componentFor components goal)))) :
    PureReturns program bindings state (a "gslt:normalized:component-for" arguments) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.componentFor components goal))) :=
  binary_call .componentFor "components" "goal" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem componentFor_body_returns (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goal : TopDownMatchDerivatives.Goal Term) :
    PureReturns program
      (binaryEnvironment "components" "goal" (encoded (encodeList (encodeList goalTerm) components)) (encoded (goalTerm goal)))
      state (rawEquation .componentFor).body state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.componentFor components goal))) := by
  induction components with
  | nil =>
      let bindings := binaryEnvironment "components" "goal" (encoded (encodeList (encodeList goalTerm) [])) (encoded (goalTerm goal))
      rw [componentFor_shape]
      apply case_returns program bindings bindings state state state (v "components") (.symbol "LNil")
        (a "LCons" [v "goal", .symbol "LNil"]) _ _ componentForCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "components"
      · simp [componentForCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template program (a "LCons" [v "goal", .symbol "LNil"]) := by
          apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
          intro argument member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact .captured _
          · exact .symbol _
        simpa [TopDownMatchDerivativeNormalization.componentFor, bindings, binaryEnvironment,
          encodeList, applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program bindings state _ template
  | cons first rest ih =>
      let bindings := binaryEnvironment "components" "goal"
        (encoded (encodeList (encodeList goalTerm) (first :: rest))) (encoded (goalTerm goal))
      let selected := ("rest", encoded (encodeList (encodeList goalTerm) rest)) ::
        ("first", encoded (encodeList goalTerm first)) :: bindings
      rw [componentFor_shape]
      apply case_returns program bindings selected state state state (v "components")
        (encoded (encodeList (encodeList goalTerm) (first :: rest))) componentForCons _ _ componentForCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "components"
      · simp [componentForCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply if_returns program selected state state state _ _ _ _ _
          (member_goal_variables_returns selected state goal first "goal" "first"
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
            (by simp [selected, applySubst, Subst.lookup]))
        by_cases present : goal ∈ first
        · simpa [present, Effects.boolean, TopDownMatchDerivativeNormalization.componentFor,
            selected, applySubst, Subst.lookup] using variable_returns program selected state "first"
        · simpa [present, Effects.boolean, TopDownMatchDerivativeNormalization.componentFor] using
            componentFor_call selected state rest goal _
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih

theorem componentFor_captured_returns (bindings : Subst) (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goal : TopDownMatchDerivatives.Goal Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList goalTerm) components), encoded (goalTerm goal)]) :
    PureReturns program bindings state (a "gslt:normalized:component-for" arguments) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.componentFor components goal))) :=
  componentFor_call bindings state components goal arguments captured (componentFor_body_returns state components goal)

/-- The source's temporary displacement/residual pair uses the existing
position and goal encodings; it introduces no pattern or state semantics. -/
def factorTerm (factor : Position × TopDownMatchDerivatives.Goal Term) : Term :=
  .application "MFactor" [positionTerm factor.1, goalTerm factor.2]

private def factorsPairs : List (Atom × Atom) :=
  [(v "component", a "gslt:normalized:component-for" [v "components", v "first"]),
   (v "base", a "gslt:normalized:base" [v "component"]),
   (v "relative", a "gslt:normalized:rebase" [v "base", v "first"]),
   (v "tail", a "gslt:normalized:factors" [v "components", v "rest"])]

private def factorsResult : Atom := a "LCons" [a "MFactor" [v "base", v "relative"], v "tail"]

private def factorsCons : Atom :=
  a "let*" [.expression (factorsPairs.map fun row => .expression [row.1, row.2]), factorsResult]

private def factorsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "first", v "rest"], factorsCons)]

private theorem factors_shape : (rawEquation .factors).body =
    a "case" [v "goals", .expression (factorsCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem factors_call (bindings : Subst) (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goals : List (TopDownMatchDerivatives.Goal Term))
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList goalTerm) components), encoded (encodeList goalTerm goals)])
    (computed : PureReturns program
      (binaryEnvironment "components" "goals" (encoded (encodeList (encodeList goalTerm) components)) (encoded (encodeList goalTerm goals)))
      state (rawEquation .factors).body state
      (encoded (encodeList factorTerm (goals.map fun goal =>
        let base := TopDownMatchDerivativeNormalization.componentBase (TopDownMatchDerivativeNormalization.componentFor components goal)
        (base, TopDownMatchDerivativeNormalization.relativize base goal))))) :
    PureReturns program bindings state (a "gslt:normalized:factors" arguments) state
      (encoded (encodeList factorTerm (goals.map fun goal =>
        let base := TopDownMatchDerivativeNormalization.componentBase (TopDownMatchDerivativeNormalization.componentFor components goal)
        (base, TopDownMatchDerivativeNormalization.relativize base goal)))) :=
  binary_call .factors "components" "goals" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem factors_body_returns (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program
      (binaryEnvironment "components" "goals" (encoded (encodeList (encodeList goalTerm) components)) (encoded (encodeList goalTerm goals)))
      state (rawEquation .factors).body state
      (encoded (encodeList factorTerm (goals.map fun goal =>
        let base := TopDownMatchDerivativeNormalization.componentBase (TopDownMatchDerivativeNormalization.componentFor components goal)
        (base, TopDownMatchDerivativeNormalization.relativize base goal)))) := by
  induction goals with
  | nil =>
      let bindings := binaryEnvironment "components" "goals" (encoded (encodeList (encodeList goalTerm) components)) (encoded (encodeList goalTerm []))
      rw [factors_shape]
      apply case_returns program bindings bindings state state state (v "goals") (.symbol "LNil")
        (.symbol "LNil") _ _ factorsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "goals"
      · simp [factorsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := binaryEnvironment "components" "goals" (encoded (encodeList (encodeList goalTerm) components))
        (encoded (encodeList goalTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList goalTerm rest)) :: ("first", encoded (goalTerm first)) :: bindings
      let component := TopDownMatchDerivativeNormalization.componentFor components first
      let componentBound := ("component", encoded (encodeList goalTerm component)) :: selected
      let base := TopDownMatchDerivativeNormalization.componentBase component
      let baseBound := ("base", encoded (positionTerm base)) :: componentBound
      let relative := TopDownMatchDerivativeNormalization.relativize base first
      let relativeBound := ("relative", encoded (goalTerm relative)) :: baseBound
      let tail := encoded (encodeList factorTerm (rest.map fun goal =>
        let displacement := TopDownMatchDerivativeNormalization.componentBase (TopDownMatchDerivativeNormalization.componentFor components goal)
        (displacement, TopDownMatchDerivativeNormalization.relativize displacement goal)))
      let tailBound := ("tail", tail) :: relativeBound
      rw [factors_shape]
      apply case_returns program bindings selected state state state (v "goals")
        (encoded (encodeList goalTerm (first :: rest))) factorsCons _ _ factorsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "goals"
      · simp [factorsCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply PureData.let_bindings_return (program := program) (bindings := selected) (before := state) (middle := state)
          (pairs := factorsPairs) (final := tailBound) _ state factorsResult _ _
        · apply PureData.BindingsReturn.cons (bound := componentBound) (value := encoded (encodeList goalTerm component))
          · exact componentFor_captured_returns selected state components first _
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
          · simp [componentBound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
              SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := baseBound) (value := encoded (positionTerm base))
            · exact base_captured_returns componentBound state component (v "component")
                (by simp [componentBound, applySubst, Subst.lookup])
            · simp [baseBound, componentBound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := relativeBound) (value := encoded (goalTerm relative))
              · exact rebase_captured_returns baseBound state base first _
                  (by simp [baseBound, componentBound, selected, applySubst, Subst.lookup])
              · simp [relativeBound, baseBound, componentBound, selected, bindings, binaryEnvironment,
                  SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := tailBound) (value := tail)
                · exact factors_call relativeBound state components rest _
                    (by simp [relativeBound, baseBound, componentBound, selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
                · simp [tailBound, relativeBound, baseBound, componentBound, selected, bindings, binaryEnvironment,
                    SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                · exact .nil _ _
        · have template : PureData.Template program factorsResult := by
            apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
            intro argument member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · apply PureData.Template.constructor "MFactor" _ (by decide +kernel) (by decide)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> exact .captured _
            · exact .captured _
          simpa [factorsResult, factorTerm, tailBound, tail, relativeBound, relative, baseBound, base,
            componentBound, component, selected, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return program tailBound state _ template

theorem factors_captured_returns (bindings : Subst) (state : State)
    (components : List (List (TopDownMatchDerivatives.Goal Term))) (goals : List (TopDownMatchDerivatives.Goal Term))
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList goalTerm) components), encoded (encodeList goalTerm goals)]) :
    PureReturns program bindings state (a "gslt:normalized:factors" arguments) state
      (encoded (encodeList factorTerm (goals.map fun goal =>
        let base := TopDownMatchDerivativeNormalization.componentBase (TopDownMatchDerivativeNormalization.componentFor components goal)
        (base, TopDownMatchDerivativeNormalization.relativize base goal)))) :=
  factors_call bindings state components goals arguments captured (factors_body_returns state components goals)

private def controlsCons : Atom :=
  a "let" [v "tail", a "gslt:normalized:controls" [v "rest"], a "LCons" [v "pending", v "tail"]]

private def controlsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "MFactor" [v "base", a "MGoal" [v "announcement", v "pending"]], v "rest"], controlsCons)]

private theorem controls_shape : (rawEquation .controls).body =
    a "case" [v "factors", .expression (controlsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem controls_call (bindings : Subst) (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList factorTerm factors))
    (computed : PureReturns program (unaryEnvironment "factors" (encoded (encodeList factorTerm factors)))
      state (rawEquation .controls).body state
      (encoded (encodeList (encodeList obligationTerm) (factors.map fun factor => factor.2.pending)))) :
    PureReturns program bindings state (a "gslt:normalized:controls" [argument]) state
      (encoded (encodeList (encodeList obligationTerm) (factors.map fun factor => factor.2.pending))) :=
  unary_call .controls "factors" bindings state argument _ _ rfl (by decide +kernel) captured computed

private theorem controls_body_returns (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term)) :
    PureReturns program (unaryEnvironment "factors" (encoded (encodeList factorTerm factors)))
      state (rawEquation .controls).body state
      (encoded (encodeList (encodeList obligationTerm) (factors.map fun factor => factor.2.pending))) := by
  induction factors with
  | nil =>
      let bindings := unaryEnvironment "factors" (encoded (encodeList factorTerm []))
      rw [controls_shape]
      apply case_returns program bindings bindings state state state (v "factors") (.symbol "LNil")
        (.symbol "LNil") _ _ controlsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "factors"
      · simp [controlsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := unaryEnvironment "factors" (encoded (encodeList factorTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList factorTerm rest)) :: ("pending", encoded (encodeList obligationTerm first.2.pending)) ::
        ("announcement", encoded (locationTerm first.2.location)) :: ("base", encoded (positionTerm first.1)) :: bindings
      let tail := encoded (encodeList (encodeList obligationTerm) (rest.map fun factor => factor.2.pending))
      let bound := ("tail", tail) :: selected
      rw [controls_shape]
      apply case_returns program bindings selected state state state (v "factors")
        (encoded (encodeList factorTerm (first :: rest))) controlsCons _ _ controlsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, unaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "factors"
      · simp [controlsCases, encodeList, factorTerm, goalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, unaryEnvironment]
      · apply let_returns program selected bound state state state (v "tail")
          (a "gslt:normalized:controls" [v "rest"]) (a "LCons" [v "pending", v "tail"]) tail _
        · exact controls_call selected state rest (v "rest") (by simp [selected, applySubst, Subst.lookup]) ih
        · simp [bound, selected, bindings, unaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · simpa [bound, tail, selected, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program bound state _ (cons_template_named "pending" "tail")

theorem controls_captured_returns (bindings : Subst) (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList factorTerm factors)) :
    PureReturns program bindings state (a "gslt:normalized:controls" [argument]) state
      (encoded (encodeList (encodeList obligationTerm) (factors.map fun factor => factor.2.pending))) :=
  controls_call bindings state factors argument captured (controls_body_returns state factors)

private theorem control_index (controls : List (List (TopDownMatchDerivatives.Obligation Term)))
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    (controls.map (encodeList obligationTerm)).idxOf (encodeList obligationTerm pending) = controls.idxOf pending := by
  induction controls with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first = pending
      · subst first
        simp
      · have different : encodeList obligationTerm first ≠ encodeList obligationTerm pending :=
          (encodeList_injective obligationTerm obligationTerm_injective).ne same
        simp [same, different, ih]

private def instancesPairs : List (Atom × Atom) :=
  [(v "index", a "gslt:normalized:index" [v "pending", v "controls"]),
   (v "tail", a "gslt:normalized:instances" [v "rest", v "controls"])]

private def instancesResult : Atom :=
  a "LCons" [a "MInstance" [v "base", v "announcement", v "index"], v "tail"]

private def instancesCons : Atom :=
  a "let*" [.expression (instancesPairs.map fun row => .expression [row.1, row.2]), instancesResult]

private def instancesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "MFactor" [v "base", a "MGoal" [v "announcement", v "pending"]], v "rest"], instancesCons)]

private theorem instances_shape : (rawEquation .instances).body =
    a "case" [v "factors", .expression (instancesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem instances_call (bindings : Subst) (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term))
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList factorTerm factors), encoded (encodeList (encodeList obligationTerm) controls)])
    (computed : PureReturns program
      (binaryEnvironment "factors" "controls" (encoded (encodeList factorTerm factors)) (encoded (encodeList (encodeList obligationTerm) controls)))
      state (rawEquation .instances).body state
      (encoded (encodeList instanceTerm (factors.map fun factor =>
        ⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩)))) :
    PureReturns program bindings state (a "gslt:normalized:instances" arguments) state
      (encoded (encodeList instanceTerm (factors.map fun factor =>
        ⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩))) :=
  binary_call .instances "factors" "controls" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem instances_body_returns (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term))
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) :
    PureReturns program
      (binaryEnvironment "factors" "controls" (encoded (encodeList factorTerm factors)) (encoded (encodeList (encodeList obligationTerm) controls)))
      state (rawEquation .instances).body state
      (encoded (encodeList instanceTerm (factors.map fun factor =>
        ⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩))) := by
  induction factors with
  | nil =>
      let bindings := binaryEnvironment "factors" "controls" (encoded (encodeList factorTerm [])) (encoded (encodeList (encodeList obligationTerm) controls))
      rw [instances_shape]
      apply case_returns program bindings bindings state state state (v "factors") (.symbol "LNil")
        (.symbol "LNil") _ _ instancesCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "factors"
      · simp [instancesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := binaryEnvironment "factors" "controls" (encoded (encodeList factorTerm (first :: rest)))
        (encoded (encodeList (encodeList obligationTerm) controls))
      let selected := ("rest", encoded (encodeList factorTerm rest)) :: ("pending", encoded (encodeList obligationTerm first.2.pending)) ::
        ("announcement", encoded (locationTerm first.2.location)) :: ("base", encoded (positionTerm first.1)) :: bindings
      let indexBound := ("index", number (controls.idxOf first.2.pending)) :: selected
      let tail := encoded (encodeList instanceTerm (rest.map fun factor =>
        ⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩))
      let tailBound := ("tail", tail) :: indexBound
      rw [instances_shape]
      apply case_returns program bindings selected state state state (v "factors")
        (encoded (encodeList factorTerm (first :: rest))) instancesCons _ _ instancesCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "factors"
      · simp [instancesCases, encodeList, factorTerm, goalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply PureData.let_bindings_return (program := program) (bindings := selected) (before := state) (middle := state)
          (pairs := instancesPairs) (final := tailBound) _ state instancesResult _ _
        · apply PureData.BindingsReturn.cons (bound := indexBound) (value := number (controls.idxOf first.2.pending))
          · simpa only [control_index] using index_captured_returns selected state (encodeList obligationTerm first.2.pending)
              (controls.map (encodeList obligationTerm)) [v "pending", v "controls"]
              (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup, listValue, encodeList_map])
          · simp [indexBound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
              SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := tailBound) (value := tail)
            · exact instances_call indexBound state rest controls _
                (by simp [indexBound, selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
            · simp [tailBound, indexBound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact .nil _ _
        · have template : PureData.Template program instancesResult := by
            apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
            intro argument member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · apply PureData.Template.constructor "MInstance" _ (by decide +kernel) (by decide)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl <;> exact .captured _
            · exact .captured _
          simpa [instancesResult, instanceTerm, tailBound, tail, indexBound, selected, encodeList,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program tailBound state _ template

theorem instances_captured_returns (bindings : Subst) (state : State)
    (factors : List (Position × TopDownMatchDerivatives.Goal Term))
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList factorTerm factors), encoded (encodeList (encodeList obligationTerm) controls)]) :
    PureReturns program bindings state (a "gslt:normalized:instances" arguments) state
      (encoded (encodeList instanceTerm (factors.map fun factor =>
        ⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩))) :=
  instances_call bindings state factors controls arguments captured (instances_body_returns state factors controls)

private def normalizePairs : List (Atom × Atom) :=
  [(v "components", a "gslt:normalized:components" [v "goals"]),
   (v "factors", a "gslt:normalized:factors" [v "components", v "goals"]),
   (v "all", a "gslt:normalized:controls" [v "factors"]),
   (v "controls", a "gslt:automata:unique" [v "all"]),
   (v "instances", a "gslt:normalized:instances" [v "factors", v "controls"])]

private def normalizeResult : Atom := a "MNormal" [v "controls", v "instances"]

private theorem normalize_shape : (rawEquation .normalize).body =
    a "let*" [.expression (normalizePairs.map fun row => .expression [row.1, row.2]), normalizeResult] := by decide +kernel

/-- The retained source constructs overlap components, rebases their goals,
stably interns residual controls and restores original instance order. -/
theorem normalize_captured_returns (bindings : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst bindings argument = encoded (encodeList goalTerm goals)) :
    PureReturns program bindings state (a "gslt:normalized:normalize" [argument]) state
      (encoded (normalTerm (TopDownMatchDerivativeNormalization.normalize goals))) := by
  apply unary_call .normalize "goals" bindings state argument _ _ rfl (by decide +kernel) captured
  let callee := unaryEnvironment "goals" (encoded (encodeList goalTerm goals))
  let components := TopDownMatchDerivativeNormalization.dependencyComponents goals
  let componentsBound := ("components", encoded (encodeList (encodeList goalTerm) components)) :: callee
  let factors := goals.map (TopDownMatchDerivativeNormalization.factor goals)
  let factorsBound := ("factors", encoded (encodeList factorTerm factors)) :: componentsBound
  let all := factors.map fun factor => factor.2.pending
  let allBound := ("all", encoded (encodeList (encodeList obligationTerm) all)) :: factorsBound
  let controls := all.eraseDups
  let controlsBound := ("controls", encoded (encodeList (encodeList obligationTerm) controls)) :: allBound
  let instances := factors.map fun factor => (⟨factor.1, factor.2.location, controls.idxOf factor.2.pending⟩ : Instance)
  let instancesBound := ("instances", encoded (encodeList instanceTerm instances)) :: controlsBound
  rw [normalize_shape]
  apply PureData.let_bindings_return (program := program) (bindings := callee) (before := state) (middle := state)
    (pairs := normalizePairs) (final := instancesBound) _ state normalizeResult _ _
  · apply PureData.BindingsReturn.cons (bound := componentsBound) (value := encoded (encodeList (encodeList goalTerm) components))
    · exact components_captured_returns callee state goals (v "goals")
        (by simp [callee, unaryEnvironment, applySubst, Subst.lookup])
    · simp [componentsBound, callee, unaryEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := factorsBound) (value := encoded (encodeList factorTerm factors))
      · exact factors_captured_returns componentsBound state components goals _
          (by simp [componentsBound, callee, unaryEnvironment, applySubst, Subst.lookup])
      · simp [factorsBound, componentsBound, callee, unaryEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := allBound) (value := encoded (encodeList (encodeList obligationTerm) all))
        · exact controls_captured_returns factorsBound state factors (v "factors")
            (by simp [factorsBound, applySubst, Subst.lookup])
        · simp [allBound, factorsBound, componentsBound, callee, unaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := controlsBound) (value := encoded (encodeList (encodeList obligationTerm) controls))
          · have old := MatchAutomataInventoryExecution.unique_captured_returns allBound state
              (all.map (encodeList obligationTerm)) (v "all")
              (by simp [allBound, applySubst, Subst.lookup, listValue, encodeList_map])
            have same := Mettapedia.OSLF.Framework.CarrierObjectClosure.eraseDups_map_of_injective
              (encodeList obligationTerm) (encodeList_injective obligationTerm obligationTerm_injective) all
            simpa only [same, listValue, encodeList_map, Function.comp_def, id_eq] using
              automata_captured_returns (by decide +kernel) old
          · simp [controlsBound, allBound, factorsBound, componentsBound, callee, unaryEnvironment,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := instancesBound) (value := encoded (encodeList instanceTerm instances))
            · exact instances_captured_returns controlsBound state factors controls _
                (by simp [controlsBound, allBound, factorsBound, applySubst, Subst.lookup])
            · simp [instancesBound, controlsBound, allBound, factorsBound, componentsBound, callee, unaryEnvironment,
                SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact .nil _ _
  · have template : PureData.Template program normalizeResult := by
      apply PureData.Template.constructor "MNormal" _ (by decide +kernel) (by decide)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .captured _
    simpa [normalizeResult, TopDownMatchDerivativeNormalization.normalize, normalTerm, instancesBound, instances,
      controlsBound, controls, allBound, all, factorsBound, factors, componentsBound, encodeList, applySubst,
      applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program instancesBound state _ template

theorem normalize_returns (state : State) (goals : List (TopDownMatchDerivatives.Goal Term)) :
    PureReturns program [] state (a "gslt:normalized:normalize" [encoded (encodeList goalTerm goals)]) state
      (encoded (normalTerm (TopDownMatchDerivativeNormalization.normalize goals))) :=
  normalize_captured_returns [] state goals _ (by simp)

private def expandSelectionCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"),
   (a "Some" [v "pending"],
    a "let" [v "goal", a "gslt:normalized:restore"
      [a "MInstance" [v "offset", v "announcement", v "index"], v "pending"],
      a "LCons" [v "goal", v "tail"]])]

private def expandInstancesCons : Atom :=
  a "let" [v "tail", a "gslt:normalized:expand-instances" [v "controls", v "rest"],
    a "case" [a "gslt:normalized:at" [v "controls", v "index"],
      .expression (expandSelectionCases.map fun row => .expression [row.1, row.2])]]

private def expandInstancesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "MInstance" [v "offset", v "announcement", v "index"], v "rest"], expandInstancesCons)]

private theorem expandInstances_shape : (rawEquation .expandInstances).body =
    a "case" [v "instances", .expression (expandInstancesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem expandInstances_call (bindings : Subst) (state : State)
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) (instances : List Instance)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList obligationTerm) controls), encoded (encodeList instanceTerm instances)])
    (computed : PureReturns program
      (binaryEnvironment "controls" "instances" (encoded (encodeList (encodeList obligationTerm) controls)) (encoded (encodeList instanceTerm instances)))
      state (rawEquation .expandInstances).body state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand ⟨controls, instances⟩)))) :
    PureReturns program bindings state (a "gslt:normalized:expand-instances" arguments) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand ⟨controls, instances⟩))) :=
  binary_call .expandInstances "controls" "instances" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem expandInstances_body_returns (state : State)
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) (instances : List Instance) :
    PureReturns program
      (binaryEnvironment "controls" "instances" (encoded (encodeList (encodeList obligationTerm) controls)) (encoded (encodeList instanceTerm instances)))
      state (rawEquation .expandInstances).body state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand ⟨controls, instances⟩))) := by
  induction instances with
  | nil =>
      let bindings := binaryEnvironment "controls" "instances" (encoded (encodeList (encodeList obligationTerm) controls)) (encoded (encodeList instanceTerm []))
      rw [expandInstances_shape]
      apply case_returns program bindings bindings state state state (v "instances") (.symbol "LNil")
        (.symbol "LNil") _ _ expandInstancesCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "instances"
      · simp [expandInstancesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "LNil"
  | cons first rest ih =>
      let bindings := binaryEnvironment "controls" "instances" (encoded (encodeList (encodeList obligationTerm) controls))
        (encoded (encodeList instanceTerm (first :: rest)))
      let selected := ("rest", encoded (encodeList instanceTerm rest)) :: ("index", number first.control) ::
        ("announcement", encoded (locationTerm first.announcement)) :: ("offset", encoded (positionTerm first.displacement)) :: bindings
      let tail := encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand ⟨controls, rest⟩))
      let tailBound := ("tail", tail) :: selected
      rw [expandInstances_shape]
      apply case_returns program bindings selected state state state (v "instances")
        (encoded (encodeList instanceTerm (first :: rest))) expandInstancesCons _ _ expandInstancesCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "instances"
      · simp [expandInstancesCases, encodeList, instanceTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply let_returns program selected tailBound state state state (v "tail")
          (a "gslt:normalized:expand-instances" [v "controls", v "rest"])
          (a "case" [a "gslt:normalized:at" [v "controls", v "index"],
            .expression (expandSelectionCases.map fun row => .expression [row.1, row.2])]) tail _
        · exact expandInstances_call selected state controls rest _
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup]) ih
        · simp [tailBound, selected, bindings, binaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · have selectedControl := at_captured_returns tailBound state (controls.map (encodeList obligationTerm)) first.control
            (v "controls") (v "index")
            (by simp [tailBound, selected, bindings, binaryEnvironment, applySubst, Subst.lookup, listValue, encodeList_map])
            (by simpa [tailBound, selected, applySubst, Subst.lookup] using variable_returns program tailBound state "index")
          cases picked : controls[first.control]? with
          | none =>
              apply case_returns program tailBound tailBound state state state
                (a "gslt:normalized:at" [v "controls", v "index"]) (.symbol "None") (v "tail") _ _
                expandSelectionCases (read_cases_encoded _) _ _ _
              · simpa [List.getElem?_map, picked, termOptionTerm, CettaWireAtom.encode] using selectedControl
              · simp [expandSelectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [TopDownMatchDerivativeNormalization.expand, picked, tailBound, tail, applySubst, Subst.lookup] using
                  variable_returns program tailBound state "tail"
          | some pending =>
              let pendingBound := ("pending", encoded (encodeList obligationTerm pending)) :: tailBound
              let goal := encoded (goalTerm (instantiate first pending))
              let goalBound := ("goal", goal) :: pendingBound
              apply case_returns program tailBound pendingBound state state state
                (a "gslt:normalized:at" [v "controls", v "index"])
                (encoded (.application "Some" [encodeList obligationTerm pending]))
                (a "let" [v "goal", a "gslt:normalized:restore"
                  [a "MInstance" [v "offset", v "announcement", v "index"], v "pending"],
                  a "LCons" [v "goal", v "tail"]]) _ _ expandSelectionCases (read_cases_encoded _) _ _ _
              · simpa [List.getElem?_map, picked, termOptionTerm] using selectedControl
              · simp [expandSelectionCases, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, pendingBound, tailBound, selected, bindings, binaryEnvironment]
              · apply let_returns program pendingBound goalBound state state state (v "goal")
                  (a "gslt:normalized:restore" [a "MInstance" [v "offset", v "announcement", v "index"], v "pending"])
                  (a "LCons" [v "goal", v "tail"]) goal _
                · exact restore_captured_returns pendingBound state first pending _
                    (by simp [pendingBound, tailBound, selected, instanceTerm, applySubst,
                      applySubst.applySubstList, Subst.lookup, listValue, encodeList_map,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany])
                · simp [goalBound, pendingBound, tailBound, selected, bindings, binaryEnvironment,
                    SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                · simpa [TopDownMatchDerivativeNormalization.expand, picked, goalBound, goal, pendingBound,
                    tailBound, tail, encodeList, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return program goalBound state _ (cons_template_named "goal" "tail")

theorem expandInstances_captured_returns (bindings : Subst) (state : State)
    (controls : List (List (TopDownMatchDerivatives.Obligation Term))) (instances : List Instance)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList (encodeList obligationTerm) controls), encoded (encodeList instanceTerm instances)]) :
    PureReturns program bindings state (a "gslt:normalized:expand-instances" arguments) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand ⟨controls, instances⟩))) :=
  expandInstances_call bindings state controls instances arguments captured (expandInstances_body_returns state controls instances)

private def expandEnvironment (normal : NormalForm Term) : Subst :=
  [("instances", encoded (encodeList instanceTerm normal.instances)),
   ("controls", encoded (encodeList (encodeList obligationTerm) normal.controls))]

private theorem expand_clause (normal : NormalForm Term) :
    clauses program "gslt:normalized:expand" [encoded (normalTerm normal)] =
      [.evaluate (expandEnvironment normal) (rawEquation .expand).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:expand").filterMap _ = _
  rw [show equations "gslt:normalized:expand" = [rawEquation .expand] from rfl]
  have formals : (rawEquation .expand).arguments = [a "MNormal" [v "controls", v "instances"]] := by decide +kernel
  simp [formals, normalTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, expandEnvironment]

theorem expand_captured_returns (bindings : Subst) (state : State) (normal : NormalForm Term) (argument : Atom)
    (captured : applySubst bindings argument = encoded (normalTerm normal)) :
    PureReturns program bindings state (a "gslt:normalized:expand" [argument]) state
      (encoded (encodeList goalTerm (TopDownMatchDerivativeNormalization.expand normal))) := by
  apply raw_call .expand bindings (expandEnvironment normal) state [argument] _ _ rfl
    (by simp [captured]) (expand_clause normal)
  rw [show (rawEquation .expand).body = a "gslt:normalized:expand-instances" [v "controls", v "instances"] by decide +kernel]
  exact expandInstances_captured_returns (expandEnvironment normal) state normal.controls normal.instances _
    (by simp [expandEnvironment, applySubst, Subst.lookup])

/-- Counted execution returns the existing normal form and the number of
distinct cached derivative activations dispatched across its observations. -/
def executedTerm (result : NormalForm Term × Nat) : Term :=
  .application "MExecuted" [normalTerm result.1, .natural result.2]

private def executeFinished : Atom := a "MExecuted" [v "after", a "+" [v "count", v "later"]]

private def executeResultCases : SpaceSemantics.Cases :=
  [(a "MExecuted" [v "after", v "later"], executeFinished)]

private def executeDerived : Atom :=
  a "let" [v "next", a "gslt:normalized:normalize" [v "goals"],
    a "case" [a "gslt:normalized:execute" [v "rest", v "next"],
      .expression (executeResultCases.map fun row => .expression [row.1, row.2])]]

private def executeDerivativeCases : SpaceSemantics.Cases :=
  [(a "MFinished" [v "goals", v "count"], executeDerived)]

private def executeCons : Atom :=
  a "case" [a "gslt:normalized:derive" [v "normal", v "observation"],
    .expression (executeDerivativeCases.map fun row => .expression [row.1, row.2])]

private def executeCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "MExecuted" [v "normal", number 0]),
   (a "LCons" [v "observation", v "rest"], executeCons)]

private theorem execute_shape : (rawEquation .execute).body =
    a "case" [v "observations", .expression (executeCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem execute_call (bindings : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term)) (normal : NormalForm Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList obligationTerm observations), encoded (normalTerm normal)])
    (computed : PureReturns program
      (binaryEnvironment "observations" "normal" (encoded (encodeList obligationTerm observations)) (encoded (normalTerm normal)))
      state (rawEquation .execute).body state
      (encoded (executedTerm (TopDownMatchDerivativeNormalization.executeCounted observations normal)))) :
    PureReturns program bindings state (a "gslt:normalized:execute" arguments) state
      (encoded (executedTerm (TopDownMatchDerivativeNormalization.executeCounted observations normal))) :=
  binary_call .execute "observations" "normal" bindings state arguments _ _ _ rfl (by decide)
    (by decide +kernel) captured computed

private theorem addition_variables_returns (bindings : Subst) (state : State)
    (left right : Nat) (first second : String)
    (capturedFirst : applySubst bindings (v first) = number left)
    (capturedSecond : applySubst bindings (v second) = number right) :
    PureReturns program bindings state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns program bindings state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedFirst, capturedSecond]
  simpa only [CettaWireAtom.encode, Int.natCast_add] using StdLib.integer_addition state (left : Int) (right : Int)

private theorem execute_body_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term)) (normal : NormalForm Term) :
    PureReturns program
      (binaryEnvironment "observations" "normal" (encoded (encodeList obligationTerm observations)) (encoded (normalTerm normal)))
      state (rawEquation .execute).body state
      (encoded (executedTerm (TopDownMatchDerivativeNormalization.executeCounted observations normal))) := by
  induction observations generalizing normal with
  | nil =>
      let bindings := binaryEnvironment "observations" "normal" (encoded (encodeList obligationTerm [])) (encoded (normalTerm normal))
      rw [execute_shape]
      apply case_returns program bindings bindings state state state (v "observations") (.symbol "LNil")
        (a "MExecuted" [v "normal", number 0]) _ _ executeCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program bindings state "observations"
      · simp [executeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template program (a "MExecuted" [v "normal", number 0]) := by
          apply PureData.Template.constructor "MExecuted" _ (by decide +kernel) (by decide)
          intro argument member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact .captured _
          · exact .grounded _
        simpa [TopDownMatchDerivativeNormalization.executeCounted, executedTerm, bindings, binaryEnvironment,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program bindings state _ template
  | cons observation rest ih =>
      let bindings := binaryEnvironment "observations" "normal" (encoded (encodeList obligationTerm (observation :: rest)))
        (encoded (normalTerm normal))
      let selected := ("rest", encoded (encodeList obligationTerm rest)) ::
        ("observation", encoded (obligationTerm observation)) :: bindings
      let goals := TopDownMatchDerivativeNormalization.deriveShared normal observation
      let count := (TopDownMatchDerivativeNormalization.activations normal).length
      let derivedBound := ("count", number count) :: ("goals", encoded (encodeList goalTerm goals)) :: selected
      let next := TopDownMatchDerivativeNormalization.normalize goals
      let nextBound := ("next", encoded (normalTerm next)) :: derivedBound
      let after := TopDownMatchDerivativeNormalization.executeCounted rest next
      let afterBound := ("later", number after.2) :: ("after", encoded (normalTerm after.1)) :: nextBound
      rw [execute_shape]
      apply case_returns program bindings selected state state state (v "observations")
        (encoded (encodeList obligationTerm (observation :: rest))) executeCons _ _ executeCases (read_cases_encoded _) _ _ _
      · simpa [bindings, binaryEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "observations"
      · simp [executeCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, binaryEnvironment]
      · apply case_returns program selected derivedBound state state state
          (a "gslt:normalized:derive" [v "normal", v "observation"]) (encoded (resultTerm normal observation))
          executeDerived _ _ executeDerivativeCases (read_cases_encoded _) _ _ _
        · exact derivative_captured_returns selected state normal observation _
            (by simp [selected, bindings, binaryEnvironment, applySubst, Subst.lookup])
        · simp [executeDerivativeCases, resultTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, derivedBound, count, goals, selected, bindings, binaryEnvironment]
        · apply let_returns program derivedBound nextBound state state state (v "next")
            (a "gslt:normalized:normalize" [v "goals"])
            (a "case" [a "gslt:normalized:execute" [v "rest", v "next"],
              .expression (executeResultCases.map fun row => .expression [row.1, row.2])])
            (encoded (normalTerm next)) _
          · exact normalize_captured_returns derivedBound state goals (v "goals")
              (by simp [derivedBound, applySubst, Subst.lookup])
          · simp [nextBound, derivedBound, selected, bindings, binaryEnvironment,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply case_returns program nextBound afterBound state state state
              (a "gslt:normalized:execute" [v "rest", v "next"]) (encoded (executedTerm after)) executeFinished
              _ _ executeResultCases (read_cases_encoded _) _ _ _
            · exact execute_call nextBound state rest next _
                (by simp [nextBound, derivedBound, selected, applySubst, Subst.lookup]) (ih next)
            · simp [executeResultCases, executedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, afterBound, nextBound, derivedBound, selected, bindings, binaryEnvironment]
            · have leftReturned : PureReturns program afterBound state (v "after") state (encoded (normalTerm after.1)) := by
                simpa [afterBound, applySubst, Subst.lookup] using variable_returns program afterBound state "after"
              have rightReturned := addition_variables_returns afterBound state count after.2 "count" "later"
                (by simp [afterBound, nextBound, derivedBound, applySubst, Subst.lookup])
                (by simp [afterBound, applySubst, Subst.lookup])
              have returned := binary_constructor_returns program afterBound state state state "MExecuted"
                (v "after") (a "+" [v "count", v "later"]) (encoded (normalTerm after.1)) (number (count + after.2))
                (by decide +kernel) (by decide) leftReturned rightReturned
              simpa [executeFinished, TopDownMatchDerivativeNormalization.executeCounted,
                TopDownMatchDerivativeNormalization.stepCounted, TopDownMatchDerivativeNormalization.deriveShared,
                TopDownMatchDerivativeNormalization.derivativeCache, executedTerm, after, next, goals, count,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned

theorem execute_captured_returns (bindings : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term)) (normal : NormalForm Term)
    (arguments : List Atom) (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList obligationTerm observations), encoded (normalTerm normal)]) :
    PureReturns program bindings state (a "gslt:normalized:execute" arguments) state
      (encoded (executedTerm (TopDownMatchDerivativeNormalization.executeCounted observations normal))) :=
  execute_call bindings state observations normal arguments captured (execute_body_returns state observations normal)

theorem execute_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term)) (normal : NormalForm Term) :
    PureReturns program [] state
      (a "gslt:normalized:execute" [encoded (encodeList obligationTerm observations), encoded (normalTerm normal)])
      state (encoded (executedTerm (TopDownMatchDerivativeNormalization.executeCounted observations normal))) :=
  execute_captured_returns [] state observations normal _ (by simp)

/-- Compose the existing counted relative-control executor with the existing
initial observation schedule. The count excludes normalization and lookup. -/
def countedRun (patterns : List (Pattern Term)) (subject : Subject Term) : NormalForm Term × Nat :=
  let programs := patterns.map TopDownMatchDerivatives.compile
  let observations := TopDownMatchDerivatives.observe subject
  TopDownMatchDerivativeNormalization.executeCounted observations
    (TopDownMatchDerivativeNormalization.normalize
      (observations.flatMap fun observation => TopDownMatchDerivatives.seed observation.position 0 programs))

def runTerm (patterns : List (Pattern Term)) (subject : Subject Term) : Term :=
  .application "MLocations"
    [encodeList locationTerm (TopDownMatchDerivativeNormalization.run patterns subject),
     .natural (TopDownMatchDerivatives.observe subject).length, .natural (countedRun patterns subject).2]

private theorem countedRun_completed (patterns : List (Pattern Term)) (subject : Subject Term) :
    TopDownMatchDerivatives.completed
      (TopDownMatchDerivativeNormalization.expand (countedRun patterns subject).1) =
      TopDownMatchDerivativeNormalization.run patterns subject := by
  simp only [countedRun, TopDownMatchDerivativeNormalization.executeCounted_result]
  rfl

private theorem completed_variable_returns (bindings : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (name : String)
    (captured : applySubst bindings (v name) = encoded (encodeList goalTerm goals)) :
    PureReturns program bindings state (a "gslt:automata:completed" [v name]) state
      (encoded (encodeList locationTerm (TopDownMatchDerivatives.completed goals))) := by
  have old : PureReturns MatchAutomataProgram.program bindings state (a "gslt:automata:completed" [v name]) state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm)) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] bindings state state "gslt:automata:completed"
      [listValue (goals.map goalTerm)] [v name] _ (by decide +kernel) _ (by decide) _
      (MatchAutomataDerivativeExecution.completed_returns state goals)
    · intro index bounded
      have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
      subst index
      decide +kernel
    · simp [captured, listValue, encodeList_map]
  simpa only [listValue, encodeList_map, Function.comp_def, id_eq] using
    automata_captured_returns (by
      simp only [codeWithin, expressionHeadWithin, atomsWithin_eq_all, List.all_cons, List.all_nil, Bool.and_true]
      decide +kernel) old

private def runPairs : List (Atom × Atom) :=
  [(v "programs", a "gslt:automata:programs" [v "patterns"]),
   (v "observations", a "gslt:automata:observe" [v "subject", .symbol "LNil"]),
   (v "initial", a "gslt:automata:seed-all" [v "observations", v "programs"]),
   (v "normal", a "gslt:normalized:normalize" [v "initial"]),
   (v "reads", a "gslt:automata:length" [v "observations"])]

private def runInnerPairs : List (Atom × Atom) :=
  [(v "goals", a "gslt:normalized:expand" [v "after"]),
   (v "locations", a "gslt:automata:completed" [v "goals"])]

private def runResult : Atom := a "MLocations" [v "locations", v "reads", v "dispatches"]

private def runFinished : Atom :=
  a "let*" [.expression (runInnerPairs.map fun row => .expression [row.1, row.2]), runResult]

private def runCases : SpaceSemantics.Cases :=
  [(a "MExecuted" [v "after", v "dispatches"], runFinished)]

private def runCase : Atom :=
  a "case" [a "gslt:normalized:execute" [v "observations", v "normal"],
    .expression (runCases.map fun row => .expression [row.1, row.2])]

private theorem run_shape : (rawEquation .run).body =
    a "let*" [.expression (runPairs.map fun row => .expression [row.1, row.2]), runCase] := by decide +kernel

/-- Exact source execution of normalized structural matching, including its
ordered occurrence/position list and explicit derivative-dispatch counter. -/
theorem run_captured_returns (bindings : Subst) (state : State)
    (patterns : List (Pattern Term)) (subject : Subject Term) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (encodeList shapeTerm patterns), encoded (subjectTerm subject)]) :
    PureReturns program bindings state (a "gslt:normalized:run" arguments) state
      (encoded (runTerm patterns subject)) := by
  apply binary_call .run "patterns" "subject" bindings state arguments _ _ _ rfl (by decide) (by decide +kernel) captured
  let callee := binaryEnvironment "patterns" "subject" (encoded (encodeList shapeTerm patterns)) (encoded (subjectTerm subject))
  let programs := patterns.map TopDownMatchDerivatives.compile
  let observations := TopDownMatchDerivatives.observe subject
  let initial := observations.flatMap fun observation => TopDownMatchDerivatives.seed observation.position 0 programs
  let normal := TopDownMatchDerivativeNormalization.normalize initial
  let after := countedRun patterns subject
  let goals := TopDownMatchDerivativeNormalization.expand after.1
  let locations := TopDownMatchDerivatives.completed goals
  let programsBound := ("programs", encoded (encodeList (encodeList obligationTerm) programs)) :: callee
  let observationsBound := ("observations", encoded (encodeList obligationTerm observations)) :: programsBound
  let initialBound := ("initial", encoded (encodeList goalTerm initial)) :: observationsBound
  let normalBound := ("normal", encoded (normalTerm normal)) :: initialBound
  let readsBound := ("reads", number observations.length) :: normalBound
  let afterBound := ("dispatches", number after.2) :: ("after", encoded (normalTerm after.1)) :: readsBound
  let goalsBound := ("goals", encoded (encodeList goalTerm goals)) :: afterBound
  let locationsBound := ("locations", encoded (encodeList locationTerm locations)) :: goalsBound
  rw [run_shape]
  apply PureData.let_bindings_return (program := program) (bindings := callee) (before := state) (middle := state)
    (pairs := runPairs) (final := readsBound) _ state runCase _ _
  · apply PureData.BindingsReturn.cons (bound := programsBound) (value := encoded (encodeList (encodeList obligationTerm) programs))
    · simpa only [programs, listValue, encodeList_map, Function.comp_def, id_eq] using
        automata_captured_returns (by decide +kernel)
          (MatchAutomataCompilationExecution.programs_captured_returns callee state patterns (v "patterns")
            (by simp [callee, binaryEnvironment, applySubst, Subst.lookup, listValue, encodeList_map]))
    · simp [programsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := observationsBound) (value := encoded (encodeList obligationTerm observations))
      · have shifted : TopDownMatchDerivatives.shift [] (TopDownMatchDerivatives.observe subject) =
            TopDownMatchDerivatives.observe subject := by
          change List.map id _ = _
          exact List.map_id _
        simpa only [observations, shifted, listValue, encodeList_map, Function.comp_def, id_eq] using
          automata_captured_returns (by decide +kernel)
            (MatchAutomataCompilationExecution.observe_captured_returns programsBound state subject [] (v "subject") (.symbol "LNil")
              (by simp [programsBound, callee, binaryEnvironment, applySubst, Subst.lookup]) rfl)
      · simp [observationsBound, programsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := initialBound) (value := encoded (encodeList goalTerm initial))
        · simpa only [listValue, encodeList_map, Function.comp_def, id_eq] using
            automata_captured_returns (by decide +kernel)
              (MatchAutomataCompilationExecution.seed_all_captured_returns observationsBound state observations programs
                (v "observations") (v "programs")
                (by simp [observationsBound, applySubst, Subst.lookup, listValue, encodeList_map])
                (by simp [observationsBound, programsBound, applySubst, Subst.lookup, listValue, encodeList_map]))
        · simp [initialBound, observationsBound, programsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := normalBound) (value := encoded (normalTerm normal))
          · exact normalize_captured_returns initialBound state initial (v "initial")
              (by simp [initialBound, applySubst, Subst.lookup])
          · simp [normalBound, initialBound, observationsBound, programsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
              SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := readsBound) (value := number observations.length)
            · simpa only [List.length_map] using automata_captured_returns (by decide +kernel)
                (MatchAutomataSourceExecution.length_captured_returns normalBound state (observations.map obligationTerm) (v "observations")
                  (by simp [normalBound, initialBound, observationsBound, applySubst, Subst.lookup, listValue, encodeList_map]))
            · simp [readsBound, normalBound, initialBound, observationsBound, programsBound, callee, binaryEnvironment,
                SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact .nil _ _
  · apply case_returns program readsBound afterBound state state state
      (a "gslt:normalized:execute" [v "observations", v "normal"]) (encoded (executedTerm after)) runFinished
      _ _ runCases (read_cases_encoded _) _ _ _
    · exact execute_captured_returns readsBound state observations normal _
        (by simp [readsBound, normalBound, initialBound, observationsBound, applySubst, Subst.lookup])
    · simp [runCases, executedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, afterBound, readsBound, normalBound, initialBound, observationsBound,
        programsBound, callee, binaryEnvironment]
    · apply PureData.let_bindings_return (program := program) (bindings := afterBound) (before := state) (middle := state)
        (pairs := runInnerPairs) (final := locationsBound) _ state runResult _ _
      · apply PureData.BindingsReturn.cons (bound := goalsBound) (value := encoded (encodeList goalTerm goals))
        · exact expand_captured_returns afterBound state after.1 (v "after")
            (by simp [afterBound, applySubst, Subst.lookup])
        · simp [goalsBound, afterBound, readsBound, normalBound, initialBound, observationsBound, programsBound,
            callee, binaryEnvironment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := locationsBound) (value := encoded (encodeList locationTerm locations))
          · exact completed_variable_returns goalsBound state goals "goals" (by simp [goalsBound, applySubst, Subst.lookup])
          · simp [locationsBound, goalsBound, afterBound, readsBound, normalBound, initialBound, observationsBound,
              programsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · exact .nil _ _
      · have template : PureData.Template program runResult := by
          apply PureData.Template.constructor "MLocations" _ (by decide +kernel) (by decide)
          intro argument member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact .captured _
        have same : locations = TopDownMatchDerivativeNormalization.run patterns subject := countedRun_completed patterns subject
        simpa [runResult, runTerm, same, locationsBound, goalsBound, afterBound, readsBound, normalBound,
          initialBound, observationsBound, observations, after, applySubst, applySubst.applySubstList, Subst.lookup,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return program locationsBound state _ template

open MeTTaILFirstOrderRuleCompilation (PatternPlan erasePatterns)

/-- Canonical binding observations and the normalized structural schedule's
inspection/dispatch counters. This is not a total execution-cost metric. -/
def topRunTerm (patterns : List PatternPlan) (subject : PatternPlan) : Term :=
  MatchAutomataExecution.matchRunTerm (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject)
    (TopDownMatchDerivatives.observe (MatchAutomataInventoryExecution.subjectView subject)).length
    (countedRun (patterns.map MatchAutomataInventoryExecution.patternView)
      (MatchAutomataInventoryExecution.subjectView subject)).2

private theorem top_candidates (patterns : List PatternPlan) (subject : PatternPlan) :
    TopDownMatchDerivativeNormalization.run (patterns.map MatchAutomataInventoryExecution.patternView)
      (MatchAutomataInventoryExecution.subjectView subject) =
      SubtermMatching.reference ((erasePatterns patterns).map MeTTaILSubtermMatchAutomata.View.lowerPattern)
        (MeTTaILSubtermMatchAutomata.View.lowerSubject subject.erase) := by
  rw [TopDownMatchDerivativeNormalization.run_eq_reference]
  exact MatchAutomataInventoryExecution.reference_views patterns subject

private def topPairs : List (Atom × Atom) :=
  [(v "shapes", a "gslt:automata:shapes" [v "patterns"]),
   (v "tree", a "gslt:automata:subject" [v "subject"])]

private def topResult : Atom := a "MatchRun" [v "matches", v "reads", v "dispatches"]

private def topFinished : Atom :=
  a "let" [v "matches", a "gslt:automata:complete" [v "locations", v "patterns", v "subject", .symbol "LNil"], topResult]

private def topCases : SpaceSemantics.Cases :=
  [(a "MLocations" [v "locations", v "reads", v "dispatches"], topFinished)]

private def topCase : Atom :=
  a "case" [a "gslt:normalized:run" [v "shapes", v "tree"],
    .expression (topCases.map fun row => .expression [row.1, row.2])]

private theorem top_shape : (rawEquation .top).body =
    a "let*" [.expression (topPairs.map fun row => .expression [row.1, row.2]), topCase] := by decide +kernel

/-- The retained normalized entry computes the independent canonical match
list with ordered positions, occurrences and repeated-variable bindings. -/
theorem top_captured_returns (bindings : Subst) (state : State)
    (patterns : List PatternPlan) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program bindings state (a "gslt:normalized:top" arguments) state (encoded (topRunTerm patterns subject)) := by
  apply binary_call .top "patterns" "subject" bindings state arguments _ _ _ rfl (by decide) (by decide +kernel) captured
  let callee := binaryEnvironment "patterns" "subject"
    (encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns))) (encoded (InferenceCettaWire.encodePattern subject.erase))
  let shapes := patterns.map MatchAutomataInventoryExecution.patternView
  let tree := MatchAutomataInventoryExecution.subjectView subject
  let observations := TopDownMatchDerivatives.observe tree
  let after := countedRun shapes tree
  let candidates := TopDownMatchDerivativeNormalization.run shapes tree
  let shapesBound := ("shapes", encoded (encodeList shapeTerm shapes)) :: callee
  let treeBound := ("tree", encoded (subjectTerm tree)) :: shapesBound
  let selected := ("dispatches", number after.2) :: ("reads", number observations.length) ::
    ("locations", encoded (encodeList locationTerm candidates)) :: treeBound
  let results := MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject
  let matchesBound := ("matches", encoded (MatchAutomataBindingExecution.matchesTerm results)) :: selected
  rw [top_shape]
  apply PureData.let_bindings_return (program := program) (bindings := callee) (before := state) (middle := state)
    (pairs := topPairs) (final := treeBound) _ state topCase _ _
  · apply PureData.BindingsReturn.cons (bound := shapesBound) (value := encoded (encodeList shapeTerm shapes))
    · simpa only [shapes, listValue, ← List.map_map, encodeList_map, Function.comp_def, id_eq] using
        automata_captured_returns (by decide +kernel)
          (MatchAutomataInventoryExecution.shapes_captured_returns callee state patterns (v "patterns")
            (by simp [callee, binaryEnvironment, applySubst, Subst.lookup]))
    · simp [shapesBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := treeBound) (value := encoded (subjectTerm tree))
      · exact automata_captured_returns (by decide +kernel)
          (MatchAutomataInventoryExecution.subject_captured_returns shapesBound state subject (v "subject")
            (by simp [shapesBound, callee, binaryEnvironment, applySubst, Subst.lookup]))
      · simp [treeBound, shapesBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · exact .nil _ _
  · apply case_returns program treeBound selected state state state
      (a "gslt:normalized:run" [v "shapes", v "tree"]) (encoded (runTerm shapes tree)) topFinished
      _ _ topCases (read_cases_encoded _) _ _ _
    · exact run_captured_returns treeBound state shapes tree _
        (by simp [treeBound, shapesBound, applySubst, Subst.lookup])
    · simp [topCases, runTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, selected, candidates, after, observations, treeBound, shapesBound, callee, binaryEnvironment]
    · apply let_returns program selected matchesBound state state state (v "matches")
        (a "gslt:automata:complete" [v "locations", v "patterns", v "subject", .symbol "LNil"]) topResult
        (encoded (MatchAutomataBindingExecution.matchesTerm results)) _
      · have old := MatchAutomataBindingExecution.complete_captured_returns selected state candidates patterns subject
          [v "locations", v "patterns", v "subject", .symbol "LNil"]
          (by
            simp [selected, treeBound, shapesBound, callee, binaryEnvironment, applySubst, Subst.lookup]
            rfl)
        simpa only [candidates, shapes, tree, top_candidates, MeTTaILSubtermMatchAutomata.complete_reference] using
          automata_captured_returns (by decide +kernel) old
      · simp [matchesBound, selected, treeBound, shapesBound, callee, binaryEnvironment,
          SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · have template : PureData.Template program topResult := by
          apply PureData.Template.constructor "MatchRun" _ (by decide +kernel) (by decide)
          intro argument member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact .captured _
        simpa [topResult, topRunTerm, MatchAutomataExecution.matchRunTerm, matchesBound, results, selected,
          after, shapes, tree, observations, applySubst, applySubst.applySubstList, Subst.lookup,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return program matchesBound state _ template

theorem top_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)),
        encoded (InferenceCettaWire.encodePattern subject.erase)]) state (encoded (topRunTerm patterns subject)) :=
  top_captured_returns [] state patterns subject _ (by simp)

theorem top_completed_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      { state, control := .evaluate []
          (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)),
            encoded (InferenceCettaWire.encodePattern subject.erase)]) } = .complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (top_returns state patterns subject) after answers input output

theorem top_derivation_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)),
            encoded (InferenceCettaWire.encodePattern subject.erase)]) } (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (top_returns state patterns subject) after answers input output


/-- The retained source realizes the concrete normalized matcher in the shared
ordered binding contract, with its separately instrumented dispatch counters. -/
theorem top_matching_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)),
        encoded (InferenceCettaWire.encodePattern subject.erase)]) state
      (encoded (MatchAutomataExecution.matchRunTerm
        (MeTTaILSubtermMatchAutomata.normalizedTopDown (erasePatterns patterns) subject)
        (TopDownMatchDerivatives.observe (MatchAutomataInventoryExecution.subjectView subject)).length
        (countedRun (patterns.map MatchAutomataInventoryExecution.patternView)
          (MatchAutomataInventoryExecution.subjectView subject)).2)) := by
  simpa only [MeTTaILSubtermMatchAutomata.normalizedTopDown_eq_reference, topRunTerm] using
    top_returns state patterns subject

#print axioms top_matching_returns

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef RewriteRule)
open MatchAutomataExecution (matchingProjectionTerm)

private def languageTopBody : Atom :=
  a "let" [v "patterns", a "gslt:automata:language-patterns" [v "language"],
    a "gslt:normalized:top" [v "patterns", v "subject"]]

private theorem languageTop_shape : (rawEquation .languageTop).body = languageTopBody := by
  decide +kernel

/-- Matching projects the exact authored rows and retains supplied metadata.
The supplied plans certify only their first-order left patterns, not an
operational presentation, scoped binding transport or declaration typing. -/
theorem language_top_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (types terms equationRows : Term)
    (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (matchingProjectionTerm language types terms equationRows contexts premises),
       encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:normalized:language-top" arguments) state
      (encoded (topRunTerm patterns subject)) := by
  apply binary_call .languageTop "language" "subject" caller state arguments _ _ _ rfl
    (by decide) (by decide +kernel) captured
  let callee := binaryEnvironment "language" "subject"
    (encoded (matchingProjectionTerm language types terms equationRows contexts premises))
    (encoded (InferenceCettaWire.encodePattern subject.erase))
  let patternsBound :=
    ("patterns", encoded (InferenceCettaWire.encodePatterns
      (MeTTaILSubtermMatchAutomata.languagePatterns language))) :: callee
  have projected : PureReturns MatchAutomataProgram.program callee state
      (a "gslt:automata:language-patterns" [v "language"]) state
      (encoded (InferenceCettaWire.encodePatterns
        (MeTTaILSubtermMatchAutomata.languagePatterns language))) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] callee state state
      "gslt:automata:language-patterns"
      [encoded (matchingProjectionTerm language types terms equationRows contexts premises)]
      [v "language"] _ (by decide +kernel) _ (by decide) _
      (MatchAutomataExecution.language_patterns_returns state language types terms equationRows
        contexts premises)
    · intro index bounded
      have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
      subst index
      decide +kernel
    · simp [callee, binaryEnvironment, applySubst, Subst.lookup]
  rw [languageTop_shape]
  apply let_returns program callee patternsBound state state state (v "patterns")
    (a "gslt:automata:language-patterns" [v "language"])
    (a "gslt:normalized:top" [v "patterns", v "subject"]) _ _
  · exact automata_captured_returns (by decide +kernel) projected
  · simp [patternsBound, callee, binaryEnvironment, SpaceSemantics.matchBinding,
      SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · exact top_captured_returns patternsBound state patterns subject _
      (by simp [patternsBound, callee, binaryEnvironment, applySubst, Subst.lookup, admitted])

def languageTopQueryTerm (language : LanguageDef) (types terms equationRows : Term)
    (contexts premises : RewriteRule → Term) (subject : PatternPlan) : Term :=
  .application "gslt:normalized:language-top"
    [matchingProjectionTerm language types terms equationRows contexts premises,
     InferenceCettaWire.encodePattern subject.erase]

theorem language_top_returns (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language) :
    PureReturns program [] state
      (encoded (languageTopQueryTerm language types terms equationRows contexts premises subject))
      state (encoded (topRunTerm patterns subject)) :=
  language_top_captured_returns [] state language types terms equationRows contexts premises
    patterns subject admitted _ (by simp)

theorem language_top_completed_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate []
          (encoded (languageTopQueryTerm language types terms equationRows contexts premises subject)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_top_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

theorem language_top_derivation_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (encoded (languageTopQueryTerm language types terms equationRows contexts premises subject)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_top_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

#print axioms language_top_completed_iff
#print axioms language_top_derivation_iff

#print axioms language_top_captured_returns
#print axioms language_top_returns


open MeTTaILFirstOrderRuleCompilation (RuleProgram)
open RelationPremiseExecution (providerEnv providerRowsTerm VariableSourceProgram)
open MatchAutomataBindingExecution (matchesTerm)
open Mettapedia.OSLF.MeTTaIL.Engine (rewriteStepWithPremisesUsing)

private theorem compiled_patterns (language : LanguageDef) (compiled : RuleProgram language.rewrites) :
    erasePatterns (compiled.plans.map (·.left)) = MeTTaILSubtermMatchAutomata.languagePatterns language := by
  have same := congrArg (List.map RewriteRule.left) compiled.erase_eq_source
  simpa only [MeTTaILSubtermMatchAutomata.languagePatterns, MeTTaILFirstOrderRuleCompilation.erasePatterns_eq_map,
    MeTTaILFirstOrderRuleCompilation.eraseRulePlans, List.map_map, Function.comp_def,
    MeTTaILFirstOrderRuleCompilation.RulePlan.erase] using same

private theorem language_top_compiled_returns (caller : Subst) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled),
       encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:normalized:language-top" arguments) state
      (encoded (topRunTerm (compiled.plans.map (·.left)) subject)) := by
  rw [RootRuleExecution.Matched.language_wire_eq_projection language types terms contexts compiled] at captured
  exact language_top_captured_returns caller state language types terms (.symbol "LNil") contexts _
    (compiled.plans.map (·.left)) subject (compiled_patterns language compiled) arguments captured

private def languageRootEnvironment (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Subst :=
  [("subject", encoded (InferenceCettaWire.encodePattern subject.erase)),
   ("rows", encoded (providerRowsTerm rows)),
   ("language", encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled))]

private def languageRootResultCases : SpaceSemantics.Cases :=
  [(a "MatchRun" [v "matches", v "reads", v "dispatches"],
    a "gslt:rule:matched-root-reducts" [v "rewrites", v "rows", v "matches"])]

private def languageRootMatchBody : Atom :=
  a "let" [v "matched", a "gslt:normalized:language-top" [v "language", v "subject"],
    a "case" [v "matched", .expression (languageRootResultCases.map fun row => .expression [row.1, row.2])]]

private def languageRootCases : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"],
    languageRootMatchBody)]

private theorem languageRoot_shape : (rawEquation .languageRoot).body =
    a "case" [v "language", .expression (languageRootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem languageRoot_clause (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    clauses program "gslt:normalized:language-root-reducts"
      [encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled),
       encoded (providerRowsTerm rows), encoded (InferenceCettaWire.encodePattern subject.erase)] =
      [.evaluate (languageRootEnvironment language types terms contexts compiled rows subject)
        (rawEquation .languageRoot).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:normalized:language-root-reducts").filterMap _ = _
  have unique := raw_unique .languageRoot
  simp only [RawHelper.head] at unique
  rw [unique]
  have formals : (rawEquation .languageRoot).arguments = [v "language", v "rows", v "subject"] := by
    decide +kernel
  simp [formals, languageRootEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem languageRoot_body_returns (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program (languageRootEnvironment language types terms contexts compiled rows subject) state
      (rawEquation .languageRoot).body state
      (encoded (InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase))) := by
  let caller := languageRootEnvironment language types terms contexts compiled rows subject
  let selected :=
    ("rewrites", encoded (RootRuleExecution.Conditional.rulesTerm contexts compiled.plans)) ::
    ("terms", encoded terms) :: ("types", encoded types) ::
    ("name", encoded (.string language.name)) :: caller
  let patterns := compiled.plans.map (·.left)
  let observations := MeTTaILSubtermMatchAutomata.reference
    (MeTTaILSubtermMatchAutomata.languagePatterns language) subject
  let reads := (TopDownMatchDerivatives.observe (MatchAutomataInventoryExecution.subjectView subject)).length
  let dispatches := (countedRun (patterns.map MatchAutomataInventoryExecution.patternView)
    (MatchAutomataInventoryExecution.subjectView subject)).2
  let matchValue := encoded (MatchAutomataExecution.matchRunTerm observations reads dispatches)
  let bound := ("matched", matchValue) :: selected
  let matchBound := ("dispatches", number dispatches) :: ("reads", number reads) ::
    ("matches", encoded (matchesTerm observations)) :: bound
  have matched : PureReturns program selected state
      (a "gslt:normalized:language-top" [v "language", v "subject"]) state matchValue := by
    have checked := language_top_compiled_returns selected state language types terms contexts compiled.val subject
      [v "language", v "subject"]
      (by simp [selected, caller, languageRootEnvironment, applySubst, Subst.lookup])
    simpa only [topRunTerm, VariableSourceProgram.plans, compiled_patterns, patterns, observations, reads, dispatches, matchValue] using checked
  rw [languageRoot_shape]
  apply case_returns program caller selected state state state (v "language")
    (encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled))
    languageRootMatchBody _ _ languageRootCases (read_cases_encoded _) _ _ _
  · simpa [caller, languageRootEnvironment, applySubst, Subst.lookup] using
      variable_returns program caller state "language"
  · simp [languageRootCases, RootRuleExecution.Conditional.languageTerm, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, languageRootEnvironment, VariableSourceProgram.plans]
  · unfold languageRootMatchBody
    apply let_returns program selected bound state state state (v "matched") _ _ _ _ matched _ _
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound,
        matchValue, selected, caller, languageRootEnvironment, observations]
    · apply case_returns program bound matchBound state state state (v "matched") matchValue
        (a "gslt:rule:matched-root-reducts" [v "rewrites", v "rows", v "matches"]) _ _
        languageRootResultCases (read_cases_encoded _) _ _ _
      · simpa [bound, matchValue, applySubst, Subst.lookup] using
          variable_returns program bound state "matched"
      · simp [languageRootResultCases, matchValue, MatchAutomataExecution.matchRunTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          matchBound, bound, number, selected, caller, languageRootEnvironment]
      · rw [← RootRuleExecution.Matched.run_reference_eq_frontier rows language compiled.val subject]
        apply rule_captured_returns (by decide +kernel)
        apply RootRuleExecution.Matched.matched_root_captured_returns matchBound state language contexts rows
          compiled observations (v "rewrites") (v "rows") (v "matches")
        change [_, _, _] =
          [encoded (RootRuleExecution.Conditional.rulesTerm contexts compiled.plans),
           encoded (providerRowsTerm rows), encoded (matchesTerm observations)]
        simp [matchBound, bound, selected, caller, languageRootEnvironment, applySubst, Subst.lookup]

/-- The actual normalized matcher feeds the original ordered guarded-row
continuation. The first-order row erasure and equation-free language entry
are explicit admissions; this law does not establish declaration typing. -/
theorem language_root_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled),
       encoded (providerRowsTerm rows), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:normalized:language-root-reducts" [one, two, three]) state
      (encoded (InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase))) :=
  raw_call .languageRoot caller (languageRootEnvironment language types terms contexts compiled rows subject)
    state [one, two, three] _ _ rfl captured
    (languageRoot_clause language types terms contexts compiled rows subject)
    (languageRoot_body_returns state language types terms contexts compiled rows subject)

/-- The concrete source join dispatches the same physical binding observations
as the normalized matcher. Its continuation is the original guarded-row
executor, not a new reduction semantics. -/
theorem normalized_dispatch_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (RootRuleExecution.Conditional.languageTerm language types terms contexts compiled),
       encoded (providerRowsTerm rows), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:normalized:language-root-reducts" [one, two, three]) state
      (encoded (InferenceCettaWire.encodePatterns
        (RootRuleExecution.Matched.runMatches rows language compiled.val
          (MeTTaILSubtermMatchAutomata.normalizedTopDown
            (MeTTaILSubtermMatchAutomata.languagePatterns language) subject)))) := by
  simpa only [MeTTaILSubtermMatchAutomata.normalizedTopDown_eq_reference,
    RootRuleExecution.Matched.run_reference_eq_frontier] using
      language_root_captured_returns caller state language types terms contexts compiled rows subject
        one two three captured

#print axioms normalized_dispatch_captured_returns

def languageRootQueryTerm (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Term :=
  .application "gslt:normalized:language-root-reducts"
    [RootRuleExecution.Conditional.languageTerm language types terms contexts compiled,
     providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase]

theorem language_root_returns (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) :
    PureReturns program [] state
      (encoded (languageRootQueryTerm language types terms contexts compiled rows subject)) state
      (encoded (InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase))) :=
  language_root_captured_returns [] state language types terms contexts compiled rows subject _ _ _ (by simp)

theorem language_root_completed_iff (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate []
          (encoded (languageRootQueryTerm language types terms contexts compiled rows subject)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_root_returns state language types terms contexts compiled rows subject) after answers input output

theorem language_root_derivation_iff (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (encoded (languageRootQueryTerm language types terms contexts compiled rows subject)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_root_returns state language types terms contexts compiled rows subject) after answers input output

abbrev ObservesRootReduct (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : RuleProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : Prop :=
  ∃ reducts : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (encoded (languageRootQueryTerm language types terms contexts compiled rows subject)) }
      (.complete state [encoded (InferenceCettaWire.encodePatterns reducts)] [] []) ∧ target ∈ reducts

/-- Both directions concern the original equation-free GSLT step, not the
structural candidate relation or a quotient that forgets duplicate matches. -/
theorem observes_root_iff_gslt_step (state : State)
    (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (equationFree : language.isEquationFree = true) (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    ObservesRootReduct state language types terms contexts compiled rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step
        subject.erase target := by
  rw [← RootRuleExecution.Conditional.observes_root_iff_gslt_step state language types terms contexts
    compiled rows subject equationFree target]
  simp only [ObservesRootReduct, RootRuleExecution.Conditional.ObservesRootReduct,
    language_root_derivation_iff, RootRuleExecution.Conditional.language_root_derivation_iff]

#print axioms language_root_captured_returns
#print axioms language_root_returns
#print axioms language_root_completed_iff
#print axioms language_root_derivation_iff
#print axioms observes_root_iff_gslt_step

namespace DispatchControls

def queryTerm (fixture : RootRuleExecution.Conditional.Controls.Fixture) : Term :=
  languageRootQueryTerm fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") fixture.compiled fixture.rows fixture.subject

/-- The same canonical guarded-row corpus tests this different source schedule. -/
theorem fixture_returns (fixture : RootRuleExecution.Conditional.Controls.Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true) (state : State) :
    PureReturns program [] state (encoded (queryTerm fixture)) state (encoded fixture.expectedTerm) :=
  language_root_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject

theorem incorrect_observation_refused (fixture : RootRuleExecution.Conditional.Controls.Fixture)
    (admitted : fixture.plans.all (fun plan => plan.variablePremises?.isSome) = true)
    (incorrect : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (state : State)
    (different : incorrect ≠ fixture.results) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (queryTerm fixture)) }
      (.complete state [encoded (InferenceCettaWire.encodePatterns incorrect)] [] []) := by
  intro executed
  apply RootRuleExecution.Conditional.Controls.Fixture.refuses_incorrect fixture admitted state incorrect different
  apply (RootRuleExecution.Conditional.language_root_derivation_iff state fixture.language
    (.symbol "LNil") (.symbol "LNil") (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows
    fixture.subject state _ [] []).mpr
  exact (language_root_derivation_iff state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled admitted) fixture.rows fixture.subject state _ [] []).mp executed

theorem incorrect_observations_refused (state : State) :
    ∀ control ∈ RootRuleExecution.Conditional.Controls.incorrectResults,
      ¬ DeclarativeSpec.Runs program
        { state, control := .evaluate [] (encoded (queryTerm control.1)) }
        (.complete state [encoded (InferenceCettaWire.encodePatterns control.2)] [] []) := by
  intro control member
  simp only [RootRuleExecution.Conditional.Controls.incorrectResults, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    apply incorrect_observation_refused
    · decide +kernel
    · decide +kernel

/-- Three equal query rows remain three successful physical witnesses. -/
theorem duplicate_query_witnesses_returned (state : State) :
    PureReturns program [] state
      (encoded (queryTerm RootRuleExecution.Conditional.Controls.duplicateGuardFixture)) state
      (encoded (InferenceCettaWire.encodePatterns
        [.apply "done" [], .apply "done" [], .apply "done" []])) := by
  have expected : RootRuleExecution.Conditional.Controls.duplicateGuardFixture.expectedTerm =
      InferenceCettaWire.encodePatterns [.apply "done" [], .apply "done" [], .apply "done" []] := by
    decide +kernel
  rw [← expected]
  exact fixture_returns _ (by decide +kernel) state

theorem child_match_does_not_authorize_root (state : State) :
    PureReturns program [] state
      (encoded (queryTerm RootRuleExecution.Conditional.Controls.childFixture)) state (.symbol "LNil") := by
  have expected : RootRuleExecution.Conditional.Controls.childFixture.expectedTerm = .symbol "LNil" := by
    decide +kernel
  simpa only [expected, CettaWireAtom.encode] using fixture_returns
    RootRuleExecution.Conditional.Controls.childFixture (by decide +kernel) state

end DispatchControls

#print axioms DispatchControls.fixture_returns
#print axioms DispatchControls.incorrect_observation_refused
#print axioms DispatchControls.incorrect_observations_refused
#print axioms DispatchControls.duplicate_query_witnesses_returned
#print axioms DispatchControls.child_match_does_not_authorize_root

namespace Controls

def duplicated : NormalForm Term :=
  ⟨[[⟨[0], ⟨.symbol "A", 0⟩⟩]], [⟨[1], ⟨[], 0⟩, 0⟩, ⟨[1], ⟨[], 1⟩, 0⟩]⟩

def observed : TopDownMatchDerivatives.Observation Term := ⟨[1, 0], ⟨.symbol "A", 0⟩⟩

def duplicatedResult : Term :=
  .application "MFinished"
    [encodeList goalTerm [⟨⟨[1], 0⟩, []⟩, ⟨⟨[1], 1⟩, []⟩], .natural 1]

theorem duplicate_occurrences_shared_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:derive" [encoded (normalTerm duplicated), encoded (obligationTerm observed)])
      state (encoded duplicatedResult) := by
  have returned := derivative_returns state duplicated observed
  rw [show resultTerm duplicated observed = duplicatedResult by decide +kernel] at returned
  exact returned

def displaced : NormalForm Term :=
  ⟨duplicated.controls, [⟨[1], ⟨[], 0⟩, 0⟩, ⟨[2], ⟨[], 1⟩, 0⟩]⟩

def displacedResult : Term :=
  .application "MFinished"
    [encodeList goalTerm [⟨⟨[1], 0⟩, []⟩, ⟨⟨[2], 1⟩, [⟨[2, 0], ⟨.symbol "A", 0⟩⟩]⟩], .natural 2]

theorem offsets_keep_distinct_activations_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:derive" [encoded (normalTerm displaced), encoded (obligationTerm observed)])
      state (encoded displacedResult) := by
  have returned := derivative_returns state displaced observed
  rw [show resultTerm displaced observed = displacedResult by decide +kernel] at returned
  exact returned

def invalid : NormalForm Term := ⟨[], [⟨[], ⟨[], 0⟩, 4⟩]⟩

theorem invalid_control_refused_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:derive" [encoded (normalTerm invalid), encoded (obligationTerm observed)])
      state (encoded (.application "MFinished" [.symbol "LNil", .natural 1])) := by
  have returned := derivative_returns state invalid observed
  rw [show resultTerm invalid observed = .application "MFinished" [.symbol "LNil", .natural 1]
    by decide +kernel] at returned
  exact returned

def conflicting : TopDownMatchDerivatives.Observation Term := ⟨[1, 0], ⟨.symbol "B", 0⟩⟩

theorem conflicting_key_refused_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:derive" [encoded (normalTerm duplicated), encoded (obligationTerm conflicting)])
      state (encoded (.application "MFinished" [.symbol "LNil", .natural 1])) := by
  have returned := derivative_returns state duplicated conflicting
  rw [show resultTerm duplicated conflicting = .application "MFinished" [.symbol "LNil", .natural 1]
    by decide +kernel] at returned
  exact returned

theorem absent_cached_derivative_refused_execution (state : State) (activation : Nat × Position) :
    PureReturns program [] state
      (a "gslt:normalized:lookup" [encoded (activationTerm activation), .symbol "LNil"])
      state (.symbol "None") :=
  lookup_captured_returns [] state activation [] _ (by simp [encodeList, CettaWireAtom.encode, applySubst])

def droppedResult : Term :=
  .application "MFinished" [encodeList goalTerm [⟨⟨[1], 0⟩, []⟩], .natural 1]

theorem dropping_duplicate_cannot_be_completed (state : State) :
    ¬ ∃ fuel, Eval.run program fuel
      { state, control := .evaluate []
          (a "gslt:normalized:derive" [encoded (normalTerm duplicated), encoded (obligationTerm observed)]) } =
      .complete state [encoded droppedResult] [] [] := by
  intro completed
  have exactResult := (derivative_completed_iff state duplicated observed state
    [encoded droppedResult] [] []).mp completed
  have impossible : [encoded droppedResult] ≠ [encoded (resultTerm duplicated observed)] := by
    decide +kernel
  exact impossible exactResult.2.1

def interleaved : List (TopDownMatchDerivatives.Goal Term) :=
  [⟨⟨[1], 0⟩, [⟨[1, 0], ⟨.symbol "A", 0⟩⟩, ⟨[1, 1], ⟨.symbol "B", 0⟩⟩]⟩,
   ⟨⟨[2], 0⟩, [⟨[2, 0], ⟨.symbol "A", 0⟩⟩, ⟨[2, 1], ⟨.symbol "B", 0⟩⟩]⟩,
   ⟨⟨[1], 1⟩, [⟨[1, 0], ⟨.symbol "A", 0⟩⟩, ⟨[1, 1], ⟨.symbol "B", 0⟩⟩]⟩]

def inspected : List (TopDownMatchDerivatives.Observation Term) :=
  [⟨[1, 0], ⟨.symbol "A", 0⟩⟩, ⟨[1, 1], ⟨.symbol "B", 0⟩⟩,
   ⟨[2, 0], ⟨.symbol "A", 0⟩⟩, ⟨[2, 1], ⟨.symbol "B", 0⟩⟩]

def interned : NormalForm Term :=
  ⟨[[⟨[0], ⟨.symbol "A", 0⟩⟩, ⟨[1], ⟨.symbol "B", 0⟩⟩]],
   [⟨[1], ⟨[], 0⟩, 0⟩, ⟨[2], ⟨[], 0⟩, 0⟩, ⟨[1], ⟨[], 1⟩, 0⟩]⟩

/-- Relative controls are interned once while all three ordered origins remain. -/
theorem interleaved_normalization_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:normalize" [encoded (encodeList goalTerm interleaved)]) state
      (encoded (normalTerm interned)) := by
  have returned := normalize_returns state interleaved
  rw [show normalTerm (TopDownMatchDerivativeNormalization.normalize interleaved) = normalTerm interned
    by decide +kernel] at returned
  exact returned

/-- Expansion restores every absolute position and occurrence, in authored order. -/
theorem interleaved_expansion_execution (state : State) :
    PureReturns program [] state (a "gslt:normalized:expand" [encoded (normalTerm interned)]) state
      (encoded (encodeList goalTerm interleaved)) := by
  have returned := expand_captured_returns [] state interned (encoded (normalTerm interned)) (by simp)
  rw [show TopDownMatchDerivativeNormalization.expand interned = interleaved by decide +kernel] at returned
  exact returned

def finished : NormalForm Term :=
  ⟨[[]], [⟨[1], ⟨[], 0⟩, 0⟩, ⟨[2], ⟨[], 0⟩, 0⟩, ⟨[1], ⟨[], 1⟩, 0⟩]⟩

/-- The actually executed source cache performs eight derivative dispatches;
the separate position-register realization performs twelve on the same goals.
Normalization, lookup and evaluator costs are excluded from both counters. -/
theorem interleaved_counted_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:execute" [encoded (encodeList obligationTerm inspected), encoded (normalTerm interned)])
      state (encoded (executedTerm (finished, 8))) ∧
    (TopDownMatchDerivatives.executeCounted inspected interleaved).2 = 12 := by
  constructor
  · have returned := execute_returns state inspected interned
    rw [show executedTerm (TopDownMatchDerivativeNormalization.executeCounted inspected interned) = executedTerm (finished, 8)
      by decide +kernel] at returned
    exact returned
  · decide +kernel

def reversedOrigins : NormalForm Term :=
  ⟨interned.controls, [⟨[1], ⟨[], 1⟩, 0⟩, ⟨[2], ⟨[], 0⟩, 0⟩, ⟨[1], ⟨[], 0⟩, 0⟩]⟩

/-- Interning cannot reorder distinct occurrence announcements. -/
theorem reversing_origins_cannot_be_completed (state : State) :
    ¬ ∃ fuel, Eval.run program fuel
      { state, control := .evaluate []
          (a "gslt:normalized:normalize" [encoded (encodeList goalTerm interleaved)]) } =
      .complete state [encoded (normalTerm reversedOrigins)] [] [] := by
  intro completed
  have exactResult := (pure_returns_completed_iff program [] state state _ _
    (interleaved_normalization_execution state) state [encoded (normalTerm reversedOrigins)] [] []).mp completed
  have impossible : [encoded (normalTerm reversedOrigins)] ≠ [encoded (normalTerm interned)] := by
    decide +kernel
  exact impossible exactResult.2.1

theorem wrong_cache_offset_refused_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:lookup" [encoded (activationTerm (0, [2])),
        encoded (encodeList cacheTerm [((0, [1]), some [])])]) state (.symbol "None") := by
  have returned := lookup_captured_returns [] state (0, [2]) [((0, [1]), some [])]
    [encoded (activationTerm (0, [2])), encoded (encodeList cacheTerm [((0, [1]), some [])])]
    (by simp only [List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode])
  rw [show TopDownMatchDerivativeNormalization.cachedDerivative [((0, [1]), some [])] (0, [2]) = none
    by decide +kernel] at returned
  exact returned

def unaryPattern : PatternPlan := .application "f" [.metavariable "x"]
def atomicSubject : PatternPlan := .application "f" [.application "a" []]
def unaryResults : List MeTTaILSubtermMatchAutomata.BoundMatch :=
  [⟨⟨[], 0⟩, [("x", .apply "a" [])]⟩, ⟨⟨[], 1⟩, [("x", .apply "a" [])]⟩]

/-- The actual canonical string-name wire retains duplicate bound matches. -/
theorem full_run_duplicates_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns [unaryPattern, unaryPattern])),
        encoded (InferenceCettaWire.encodePattern atomicSubject.erase)]) state
      (encoded (MatchAutomataExecution.matchRunTerm unaryResults 2 4)) := by
  have same : topRunTerm [unaryPattern, unaryPattern] atomicSubject =
      MatchAutomataExecution.matchRunTerm unaryResults 2 4 := by
    unfold topRunTerm countedRun
    congr 1 <;>
      simp only [unaryPattern, atomicSubject,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  simpa only [same] using top_returns state [unaryPattern, unaryPattern] atomicSubject

def nonlinearPattern : PatternPlan := .application "f" [.metavariable "x", .metavariable "x"]
def conflictingSubject : PatternPlan := .application "f" [.application "a" [], .application "b" []]

/-- Structural wildcard candidates still pass through canonical nonlinear binding checks. -/
theorem full_run_nonlinear_refused_execution (state : State) :
    PureReturns program [] state
      (a "gslt:normalized:top" [encoded (InferenceCettaWire.encodePatterns (erasePatterns [nonlinearPattern])),
        encoded (InferenceCettaWire.encodePattern conflictingSubject.erase)]) state
      (encoded (MatchAutomataExecution.matchRunTerm [] 3 8)) := by
  have same : topRunTerm [nonlinearPattern] conflictingSubject =
      MatchAutomataExecution.matchRunTerm [] 3 8 := by
    unfold topRunTerm countedRun
    congr 1 <;>
      simp only [nonlinearPattern, conflictingSubject,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  simpa only [same] using top_returns state [nonlinearPattern] conflictingSubject

end Controls

#print axioms matcher_program_closed
#print axioms matcher_program_agreement
#print axioms automata_captured_returns
#print axioms activationTerm_injective
#print axioms prefix_returns
#print axioms prefix_captured_returns
#print axioms at_captured_returns
#print axioms activation_captured_returns
#print axioms activations_captured_returns
#print axioms relative_returns
#print axioms relative_captured_returns
#print axioms lookup_captured_returns
#print axioms restore_captured_returns
#print axioms cache_captured_returns
#print axioms dispatch_captured_returns
#print axioms encoded_activations
#print axioms derivative_captured_returns
#print axioms derivative_returns
#print axioms derivative_completed_iff
#print axioms derivative_derivation_iff
#print axioms derivative_normalize_returns
#print axioms commonPrefix_captured_returns
#print axioms gcp_captured_returns
#print axioms drop_captured_returns
#print axioms relativePending_captured_returns
#print axioms index_captured_returns
#print axioms rebase_captured_returns
#print axioms pendingPositions_captured_returns
#print axioms positions_captured_returns
#print axioms base_captured_returns
#print axioms positionMember_captured_returns
#print axioms overlapPending_captured_returns
#print axioms overlaps_captured_returns
#print axioms touches_captured_returns
#print axioms partition_captured_returns
#print axioms components_captured_returns
#print axioms componentFor_captured_returns
#print axioms factors_captured_returns
#print axioms controls_captured_returns
#print axioms instances_captured_returns
#print axioms normalize_captured_returns
#print axioms normalize_returns
#print axioms expandInstances_captured_returns
#print axioms expand_captured_returns
#print axioms execute_captured_returns
#print axioms execute_returns
#print axioms run_captured_returns
#print axioms top_captured_returns
#print axioms top_returns
#print axioms top_completed_iff
#print axioms top_derivation_iff
#print axioms Controls.duplicate_occurrences_shared_execution
#print axioms Controls.offsets_keep_distinct_activations_execution
#print axioms Controls.invalid_control_refused_execution
#print axioms Controls.conflicting_key_refused_execution
#print axioms Controls.absent_cached_derivative_refused_execution
#print axioms Controls.dropping_duplicate_cannot_be_completed
#print axioms Controls.interleaved_normalization_execution
#print axioms Controls.interleaved_expansion_execution
#print axioms Controls.interleaved_counted_execution
#print axioms Controls.reversing_origins_cannot_be_completed
#print axioms Controls.wrong_cache_offset_refused_execution
#print axioms Controls.full_run_duplicates_execution
#print axioms Controls.full_run_nonlinear_refused_execution

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataNormalizedExecution
