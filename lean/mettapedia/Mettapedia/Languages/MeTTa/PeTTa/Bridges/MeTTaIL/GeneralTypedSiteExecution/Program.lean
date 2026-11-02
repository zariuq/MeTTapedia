import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source

/-!
# Typed occurrence and selected rule enumeration through PeTTa execution

The authored enumerator reads the original declaration, pattern and permission
wire. Its outputs use the existing typed site and rule-job codecs, retaining
physical addresses, exact binder sorts and authored typing alternatives.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution

open Mettapedia.GSLT.LanguageDef CettaWire WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts GeneralTypedSites GeneralRuleJobs
open GeneralExecutionAdmission
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Equation)
open Effects (State)
open Eval
open ScopedRuleJobReadoutExecution (siteTerm typingFrameTerm jobTerm rulePlanTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_typed_sites.metta"
    sha256 "70cbcf95d6ff191c34c3240f18ce26ac8d4289eb3990e61679ffb89cc000f01c"

def program : Program := RuleExecutionProgram.program.append source.program

theorem source_equation_count : source.program.equations.length = 19 := rfl
theorem source_no_initializers : source.program.initializers = [] := rfl
theorem source_no_facts : source.program.facts = [] := rfl

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev sitesValue (sites : List SiteData) : Atom := encoded (encodeList siteTerm sites)
private abbrev jobsValue (jobs : List Job) : Atom := encoded (encodeList jobTerm jobs)
private abbrev rulesValue (rules : List RulePlan) : Atom := encoded (encodeList rulePlanTerm rules)

def retainedHead (head : String) : Bool := head != "eval" && !(head.startsWith "gslt:sites:")

theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !retainedHead equation.head || codeWithin retainedHead equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

theorem retained_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.program program := by
  apply appended_program_agreement
  · intro equation member
    have checked : source.program.equations.all (fun equation => !retainedHead equation.head) = true := by
      decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : retainedHead equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : source.program.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !retainedHead head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : retainedHead name with
    | false => rfl
    | true => simp [selected] at row

theorem retained_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns program caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

inductive Helper where
  | take | drop | argumentPermitted | wrapApplication | wrapLambda | wrapMulti | wrapCollection
  | generate | descend | applicationRows | applicationRow | applicationChildren
  | directCollection | collectionRows | collectionRow | collectionChildren
  | crossSites | crossRules | jobs
  deriving DecidableEq

def Helper.index : Helper → Nat
  | .take => 0 | .drop => 1 | .argumentPermitted => 2 | .wrapApplication => 3
  | .wrapLambda => 4 | .wrapMulti => 5 | .wrapCollection => 6 | .generate => 7
  | .descend => 8 | .applicationRows => 9 | .applicationRow => 10 | .applicationChildren => 11
  | .directCollection => 12 | .collectionRows => 13 | .collectionRow => 14 | .collectionChildren => 15
  | .crossSites => 16 | .crossRules => 17 | .jobs => 18

def Helper.head : Helper → String
  | .take => "gslt:sites:take" | .drop => "gslt:sites:drop"
  | .argumentPermitted => "gslt:sites:argument-permitted"
  | .wrapApplication => "gslt:sites:wrap-application" | .wrapLambda => "gslt:sites:wrap-lambda"
  | .wrapMulti => "gslt:sites:wrap-multi" | .wrapCollection => "gslt:sites:wrap-collection"
  | .generate => "gslt:sites:generate" | .descend => "gslt:sites:descend"
  | .applicationRows => "gslt:sites:application-rows" | .applicationRow => "gslt:sites:application-row"
  | .applicationChildren => "gslt:sites:application-children"
  | .directCollection => "gslt:sites:direct-collection"
  | .collectionRows => "gslt:sites:collection-rows" | .collectionRow => "gslt:sites:collection-row"
  | .collectionChildren => "gslt:sites:collection-children"
  | .crossSites => "gslt:sites:cross-sites" | .crossRules => "gslt:sites:cross-rules"
  | .jobs => "gslt:sites:jobs"

def Helper.names : Helper → List String
  | .take | .drop => ["count", "items"]
  | .argumentPermitted => ["permissions", "constructor", "index"]
  | .wrapApplication => ["declaration", "constructor", "before", "index", "after", "sites"]
  | .wrapLambda => ["binder", "domain", "sites"]
  | .wrapMulti => ["arity", "binders", "domain", "sites"]
  | .wrapCollection => ["frame", "kind", "before", "index", "after", "sites"]
  | .generate | .descend => ["declarations", "free", "permissions", "bound", "expected", "source"]
  | .applicationRows => ["declarations", "free", "permissions", "bound", "expected", "constructor", "arguments", "remaining", "index"]
  | .applicationRow => ["declarations", "free", "permissions", "bound", "expected", "constructor", "arguments", "row", "declaration"]
  | .applicationChildren => ["declarations", "free", "permissions", "bound", "constructor", "arguments", "parameters", "declaration", "remaining", "index"]
  | .directCollection => ["declarations", "free", "permissions", "bound", "expected", "kind", "elements"]
  | .collectionRows => ["declarations", "free", "permissions", "bound", "expected", "kind", "elements", "remaining", "index"]
  | .collectionRow => ["declarations", "free", "permissions", "bound", "expected", "kind", "elements", "row", "declaration"]
  | .collectionChildren => ["declarations", "free", "permissions", "bound", "type", "kind", "elements", "frame", "remaining", "index"]
  | .crossSites => ["ordinal", "declaration", "sites"]
  | .crossRules => ["rules", "sites", "ordinal"]
  | .jobs => ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]

def equation (helper : Helper) : SpaceSemantics.Equation :=
  source.program.equations[helper.index]'(by cases helper <;> decide +kernel)

def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw program helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

def dataHeads : List String :=
  ["LCons", "LNil", "RuleJob", "RuleJobSite", "ContextApp", "ContextLam", "ContextMultiLam",
   "ContextCollection", "TypingApplication", "TypingLambda", "TypingMultiLambda", "TypingDirectCollection",
   "TypingAuthoredCollection", "TermSlot", "TBase", "ContextHole", "RNone"]

theorem data_template (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have checked : dataHeads.all (fun name => decide
        ((ioHead name || StdLib.known name || program.equations.any (·.head == name)) = false)) = true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp checked head member)
  · have checked : dataHeads.all (fun name => decide
        (name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"])) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp checked head member)


def executionHeadNames : List String :=
  ["+", "-", "==", "Binding", "ContextApp", "ContextCollection", "ContextLam", "ContextMultiLam",
   "FVar", "GrammarTypingV1", "GrammarTypingWrappedV1", "LCons", "LNil", "None", "OperationalPermissions", "PApp",
   "PCollection", "PLam", "PMultiLam", "PSubst", "PermissionNo", "PermissionYes", "RNone",
   "RuleJob", "RuleJobSite", "Some", "TArrow", "TBase", "TCollection", "TMultiBinder",
   "TermAbstraction", "TermMultiAbstraction", "TermSimple", "TermSlot", "TypingApplication",
   "TypingAuthoredCollection", "TypingDirectCollection", "TypingLambda", "TypingMultiLambda", "Var",
   "case", "gslt:automata:append", "gslt:automata:binding", "gslt:automata:member",
   "gslt:premise:object-pattern", "gslt:premise:object-patterns",
   "gslt:premise:parameter-representation", "gslt:premise:parameter-type",
   "gslt:premise:type-arguments", "gslt:premise:type-collection-declarations",
   "gslt:premise:type-constructors", "gslt:premise:type-elements", "gslt:premise:type-extend-count",
   "gslt:premise:type-has", "gslt:rule:row-at", "gslt:sites:application-children",
   "gslt:sites:application-row", "gslt:sites:application-rows", "gslt:sites:argument-permitted",
   "gslt:sites:collection-children", "gslt:sites:collection-row", "gslt:sites:collection-rows",
   "gslt:sites:cross-rules", "gslt:sites:cross-sites", "gslt:sites:descend",
   "gslt:sites:direct-collection", "gslt:sites:drop", "gslt:sites:generate", "gslt:sites:jobs",
   "gslt:sites:take", "gslt:sites:wrap-application", "gslt:sites:wrap-collection",
   "gslt:sites:wrap-lambda", "gslt:sites:wrap-multi", "if", "let", "let*"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem program_closed : ProgramClosed executionHeads program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : program.equations.all (fun equation =>
        !executionHeads equation.head || codeWithin executionHeads equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

/-- The full scoped runtime retains exactly the declarations and equations
used by typed occurrence discovery. -/
theorem scoped_program_agreement :
    ProgramAgreementOn executionHeads program (RuleExecutionProgram.scopedProgram.append source.program) := by
  apply programAgreementOn_of_retained_rows
  · rfl
  · rfl


open SpaceSemantics Eval BridgeKit

private def rawSupportTail : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources.drop 1).foldl
    (fun loaded part => loaded.append part.program) {equations := [], declarations := []}

private theorem append_empty (p : Program) : p.append {equations := [], declarations := []} = p := by
  cases p
  simp [Program.append]
private theorem empty_append (p : Program) : ({equations := [], declarations := []} : Program).append p = p := by
  cases p
  rfl
private theorem append_assoc (a b c : Program) : (a.append b).append c = a.append (b.append c) := by
  cases a
  cases b
  cases c
  simp [Program.append, List.append_assoc]

private theorem fold_from (parts : List ProgramQuotation.QuotedProgram) (base : Program) :
    parts.foldl (fun loaded part => loaded.append part.program) base =
      base.append (parts.foldl (fun loaded part => loaded.append part.program) {equations := [], declarations := []}) := by
  induction parts generalizing base with
  | nil => exact (append_empty base).symm
  | cons first rest ih =>
    change rest.foldl (fun loaded part => loaded.append part.program) (base.append first.program) =
      base.append (rest.foldl (fun loaded part => loaded.append part.program)
        (({equations := [], declarations := []} : Program).append first.program))
    rw [empty_append, ih (base.append first.program), ih first.program]
    exact append_assoc base first.program _

private theorem raw_physical_shape :
    RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded part => loaded.append part.program) RuleExecutionProgram.scopedProgram =
    (RuleExecutionProgram.scopedProgram.append source.program).append rawSupportTail := by
  have shape : RuleExecutionProgram.interpretedPremiseSupportSources =
      (RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel)) ::
        RuleExecutionProgram.interpretedPremiseSupportSources.drop 1 := by rfl
  conv_lhs => rw [shape, List.foldl_cons]
  have first : (RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel)).program =
      source.program := by rfl
  rw [first]
  exact fold_from _ _

private theorem raw_suffix_equations :
    ∀ equation ∈ rawSupportTail.equations, executionHeads equation.head = false := by
  have checked : rawSupportTail.equations.all (fun equation => !executionHeads equation.head) = true := by decide +kernel
  intro equation member
  have row := List.all_eq_true.mp checked equation member
  cases selected : executionHeads equation.head with
  | false => rfl
  | true => simp [selected] at row

private theorem raw_suffix_declarations :
    ∀ name types, (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) ∈ rawSupportTail.declarations →
      executionHeads name = false := by
  have checked : rawSupportTail.declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: _)] => !executionHeads name
      | _ => true) = true := by decide +kernel
  intro name types member
  have row := List.all_eq_true.mp checked (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
  cases selected : executionHeads name with
  | false => rfl
  | true => simp [selected] at row

/-- Actual appended artifacts introduce no head in the independently closed typed traversal. -/
theorem raw_agreement : ProgramAgreementOn executionHeads program RuleExecutionProgram.interpretedPremiseProgram := by
  have suffix : ProgramAgreementOn executionHeads (RuleExecutionProgram.scopedProgram.append source.program)
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded part => loaded.append part.program) RuleExecutionProgram.scopedProgram) := by
    rw [raw_physical_shape]
    exact appended_program_agreement executionHeads _ _ raw_suffix_equations raw_suffix_declarations
  exact agreement_trans (agreement_trans scoped_program_agreement suffix)
    (agreement_mono (fun _ _ => rfl) CompleteExecution.PhysicalSourceAgreement.physical_interpreted_agreement)

#print axioms raw_physical_shape
#print axioms raw_suffix_equations
#print axioms raw_suffix_declarations
#print axioms raw_agreement
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution
