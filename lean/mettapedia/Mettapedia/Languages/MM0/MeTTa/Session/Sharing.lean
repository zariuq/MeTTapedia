import Mettapedia.Languages.MM0.MeTTa.Session.ProofStore
import Mettapedia.Languages.MM0.MeTTa.Data.VectorInitialization

/-!
# Chronological sharing in the retained MM0 source

A saved initializer carries a supplied witness and an optional expected
conclusion. The witness computes its actual conclusion before this expectation
is checked. Absence of an expectation never bypasses the witness check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Sharing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Preterm ProofWitness Context)
open ListAccess (optionValue)
open Store (natural)
open TableAccess (tableValue)
open Presentation.ComputationalTyping (signatureOf)

structure Entry where
  expected : Option Preterm
  witness : ProofWitness

def entryValue (entry : Entry) : Atom :=
  .expression [.symbol "MM0:Saved", ProofResults.resultValue entry.expected, Proof.witnessValue entry.witness]

private def equation : SpaceSemantics.Equation := (serviceSource.program.equations.take 2)[1]'(by decide)
private def loopBody : Atom :=
  match equation.body with
  | .expression [_, _, yes, _] => yes
  | _ => .expression []
private def entryBody : Atom :=
  match loopBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []
private def answerBody : Atom :=
  match entryBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []
private def answerCases : SpaceSemantics.Cases :=
  match answerBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def checkedBody : Atom := (answerCases[0]'(by decide)).2

/-- This is the condition read from the actual shared-entry function. -/
def expectedGuard : Atom :=
  match checkedBody with
  | .expression [_, condition, _, _] => condition
  | _ => .expression []

private def expectedCases : SpaceSemantics.Cases :=
  [( .symbol "None", boolean true),
   (.expression [.symbol "Some", .var "wanted"], .expression [.symbol "==", .var "wanted", .var "actual"])]

private theorem expected_guard_shape : expectedGuard =
    .expression [.symbol "case", .var "expected", .expression (expectedCases.map fun row => .expression [row.1,row.2])] := by decide

/-- The optional statement is checked after the witness returns. Pattern-local
`wanted` is fresh in the actual shared-entry call environment. -/
theorem expected_guard_returns (bindings : Subst) (state : State) (expected : Option Preterm) (actual : Preterm)
    (capturedExpected : applySubst bindings (.var "expected") = ProofResults.resultValue expected)
    (capturedActual : applySubst bindings (.var "actual") = Data.preterm actual)
    (fresh : Subst.lookup bindings "wanted" = none) :
    PureReturns program bindings state expectedGuard state
      (boolean (decide (expected = none ∨ expected = some actual))) := by
  rw [expected_guard_shape]
  cases expected with
  | none =>
      apply case_returns program bindings bindings state state state (.var "expected") (.symbol "None") (boolean true) _ _ expectedCases (read_cases_encoded _)
      · simpa only [capturedExpected, ProofResults.resultValue, optionValue, Option.map_none] using variable_returns program bindings state "expected"
      · simp [expectedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool true)
  | some wanted =>
      let bound := ("wanted", Data.preterm wanted) :: bindings
      have freshLookup := fresh
      unfold Subst.lookup at freshLookup
      have actualLookup := capturedActual
      unfold applySubst Subst.lookup at actualLookup
      apply case_returns program bindings bound state state state (.var "expected") (ProofResults.resultValue (some wanted))
        (.expression [.symbol "==", .var "wanted", .var "actual"]) _ _ expectedCases (read_cases_encoded _)
      · simpa only [capturedExpected] using variable_returns program bindings state "expected"
      · simp [expectedCases, ProofResults.resultValue, optionValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, freshLookup, bound]
      · apply native_variable_call_returns program bound state state "==" ["wanted", "actual"] _ (by decide) (by decide) _ (by decide)
        simp [bound, applySubst, Subst.lookup, actualLookup, StdLib.apply, boolean]
        simp [beq_eq_decide, Data.preterm_injective.eq_iff]

theorem supplied_expectation_returns (bindings : Subst) (state : State) (expected actual : Preterm)
    (capturedExpected : applySubst bindings (.var "expected") = ProofResults.resultValue (some expected))
    (capturedActual : applySubst bindings (.var "actual") = Data.preterm actual)
    (fresh : Subst.lookup bindings "wanted" = none) :
    PureReturns program bindings state expectedGuard state (boolean (decide (expected = actual))) := by
  simpa only [Option.some_ne_none, false_or, Option.some.injEq] using expected_guard_returns bindings state (some expected) actual capturedExpected capturedActual fresh

theorem wrong_expectation_refuses (bindings : Subst) (state : State) (expected actual : Preterm) (different : expected ≠ actual)
    (capturedExpected : applySubst bindings (.var "expected") = ProofResults.resultValue (some expected))
    (capturedActual : applySubst bindings (.var "actual") = Data.preterm actual)
    (fresh : Subst.lookup bindings "wanted" = none) :
    PureReturns program bindings state expectedGuard state (boolean false) := by
  simpa only [different, decide_false] using supplied_expectation_returns bindings state expected actual capturedExpected capturedActual fresh

/-- Every initializer is checked in the preceding prefix. The last judgment
is the supplied root, with all those checked conclusions available. -/
inductive Checked (context : Context) (root : ProofWitness) (claim : Preterm) :
    Proof.Tables → List Entry → Prop where
  | root {tables : Proof.Tables} :
      ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values root claim →
      Checked context root claim tables []
  | save {tables : Proof.Tables} {entry : Entry} {remaining : List Entry} {actual : Preterm} :
      ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values entry.witness actual →
      (entry.expected = none ∨ entry.expected = some actual) →
      Checked context root claim (ProofStore.extend tables actual) remaining →
      Checked context root claim tables (entry :: remaining)

theorem checked_nil_iff (tables : Proof.Tables) (context : Context) (root : ProofWitness) (claim : Preterm) :
    Checked context root claim tables [] ↔
      ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values root claim := by
  constructor
  · intro checked; cases checked with | root given => exact given
  · exact Checked.root

theorem checked_cons_refused (tables : Proof.Tables) (context : Context) (root : ProofWitness) (claim : Preterm)
    (entry : Entry) (remaining : List Entry)
    (refused : ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values entry.witness = none) :
    ¬ Checked context root claim tables (entry :: remaining) := by
  intro checked
  cases checked with
  | save given _ _ =>
      have computed := given.eval
      rw [refused] at computed
      cases computed

theorem checked_cons_iff (tables : Proof.Tables) (context : Context) (root : ProofWitness) (claim : Preterm)
    (entry : Entry) (remaining : List Entry) (actual : Preterm)
    (computed : ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values entry.witness = some actual) :
    Checked context root claim tables (entry :: remaining) ↔
      (entry.expected = none ∨ entry.expected = some actual) ∧
      Checked context root claim (ProofStore.extend tables actual) remaining := by
  constructor
  · intro checked
    cases checked with
    | save given expected tail =>
        have same := given.eval
        rw [computed] at same
        cases Option.some.inj same
        exact ⟨expected, tail⟩
  · rintro ⟨expected, tail⟩
    exact Checked.save ((ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp computed) expected tail

/-- Checked sharing is conservative over the original hypothesis scope. -/
theorem Checked.derives {tables : Proof.Tables} {context : Context} {root : ProofWitness} {claim : Preterm}
    {entries : List Entry} (checked : Checked context root claim tables entries) :
    Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values claim := by
  induction checked with
  | root given => exact given.derives
  | @save tables entry remaining actual given _ _ ih =>
      apply (Kernel.derives_with_checked_facts_iff (saved := [actual]) ?_).mp
      · simpa only [ProofStore.extend] using ih
      · intro fact member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst fact
        exact given.derives

private def environment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) : Subst :=
  [("claim", Data.preterm claim), ("root", Proof.witnessValue root), ("index", natural index),
   ("saved", .expression (saved.map entryValue)), ("hyps", Proof.hypothesesValue tables),
   ("ctx", Data.context context), ("thms", tableValue tables.theorems),
   ("defs", tableValue tables.definitions), ("terms", tableValue tables.terms)]

private def entryEnvironment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) : Subst :=
  ("proof", Proof.witnessValue entry.witness) ::
    ("expected", ProofResults.resultValue entry.expected) :: environment tables context saved index root claim

private def answerEnvironment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (answer : Option Preterm) : Subst :=
  ("answer", ProofResults.resultValue answer) :: entryEnvironment tables context saved index root claim entry

private def checkedEnvironment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (actual : Preterm) : Subst :=
  ("actual", Data.preterm actual) :: answerEnvironment tables context saved index root claim entry (some actual)

private def publishBody : Atom :=
  match checkedBody with
  | .expression [_, _, yes, _] => yes
  | _ => .expression []

private def nextBody : Atom :=
  match publishBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private theorem equation_unique :
    program.equations.filter (fun e => e.head == "mm0:shared-entries") = [equation] := by decide

private theorem equation_formals : equation.arguments =
    [.var "terms", .var "defs", .var "thms", .var "ctx", .var "hyps", .var "saved", .var "index", .var "root", .var "claim"] := by decide

private theorem equation_shape : equation.body =
    .expression [.symbol "if", .expression [.symbol "<", .var "index", .expression [.symbol "size-atom", .var "saved"]],
      loopBody, .expression [.symbol "mm0:check-proof", .var "terms", .var "defs", .var "thms", .var "ctx", .var "hyps", .var "root", .var "claim"]] := by decide

private theorem entry_shape : loopBody =
    .expression [.symbol "let", .expression [.symbol "MM0:Saved", .var "expected", .var "proof"],
      .expression [.symbol "index-atom", .var "saved", .var "index"], entryBody] := by decide

private theorem proof_shape : entryBody =
    .expression [.symbol "let", .var "answer", .expression [.symbol "mm0:proof", .var "terms", .var "defs", .var "thms", .var "ctx", .var "hyps", .var "proof"], answerBody] := by decide

private theorem answer_shape : answerBody =
    .expression [.symbol "case", .var "answer", .expression (answerCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem answer_cases : answerCases =
    [(.expression [.symbol "Some", .var "actual"], checkedBody),
     (.symbol "None", boolean false), (.var "malformed", .symbol "MM0:Malformed")] := by decide

private theorem checked_shape : checkedBody =
    .expression [.symbol "if", expectedGuard, publishBody, boolean false] := by decide

private theorem publish_shape : publishBody =
    .expression [.symbol "let", .var "next", .expression [.symbol "mm0:vector-snoc", .var "hyps", .var "actual"], nextBody] := by decide

private theorem next_shape : nextBody =
    .expression [.symbol "mm0:shared-entries", .var "terms", .var "defs", .var "thms", .var "ctx", .var "next", .var "saved",
      .expression [.symbol "+", .var "index", .grounded (.int 1)], .var "root", .var "claim"] := by decide

private theorem clause (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) :
    clauses program "mm0:shared-entries" [tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, Proof.hypothesesValue tables,
      .expression (saved.map entryValue), natural index, Proof.witnessValue root, Data.preterm claim] =
      [.evaluate (environment tables context saved index root claim) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [equation_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

private theorem condition_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (state : State) :
    PureReturns program (environment tables context saved index root claim) state
      (.expression [.symbol "<", .var "index", .expression [.symbol "size-atom", .var "saved"]]) state
      (boolean (decide (index < saved.length))) := by
  apply native_binary_call_returns program _ state state state state "<" _ _ (natural index) (natural saved.length) _
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa [environment, applySubst, Subst.lookup] using variable_returns program
      (environment tables context saved index root claim) state "index"
  · apply native_variable_call_returns program _ state state "size-atom" ["saved"] _ (by decide) (by decide) _ (by decide)
    simp [environment, applySubst, Subst.lookup, StdLib.apply, natural]
  · simp [StdLib.apply, natural, boolean]

private theorem entries_call_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (bindings : Subst)
    (hypothesesName : String) (indexExpression : Atom) (before after : State) (answer : Bool)
    (ct : applySubst bindings (.var "terms") = tableValue tables.terms)
    (cd : applySubst bindings (.var "defs") = tableValue tables.definitions)
    (cth : applySubst bindings (.var "thms") = tableValue tables.theorems)
    (cc : applySubst bindings (.var "ctx") = Data.context context)
    (ch : applySubst bindings (.var hypothesesName) = Proof.hypothesesValue tables)
    (cs : applySubst bindings (.var "saved") = .expression (saved.map entryValue))
    (cr : applySubst bindings (.var "root") = Proof.witnessValue root)
    (cq : applySubst bindings (.var "claim") = Data.preterm claim)
    (counted : PureReturns program bindings before indexExpression before (natural index))
    (child : PureReturns program (environment tables context saved index root claim) before equation.body after (boolean answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:shared-entries", .var "terms", .var "defs", .var "thms", .var "ctx",
        .var hypothesesName, .var "saved", indexExpression, .var "root", .var "claim"]) after (boolean answer) := by
  let initial := [tableValue tables.terms, tableValue tables.definitions, tableValue tables.theorems,
    Data.context context, Proof.hypothesesValue tables, .expression (saved.map entryValue)]
  have entered := authored_function_arguments_return program bindings (environment tables context saved index root claim)
    before after "mm0:shared-entries" (initial ++ [natural index, Proof.witnessValue root, Data.preterm claim]) 9 equation.body _
    (by decide) (by decide) (by simpa only [initial, List.cons_append, List.nil_append] using clause tables context saved index root claim) child
  have last := variable_arguments_return program bindings before after (.function "mm0:shared-entries")
    ["root", "claim"] (initial ++ [natural index]) 7 _
    (by simpa [cr, cq, List.append_assoc] using entered)
  have rest := evaluated_argument_returns program bindings before before after (.function "mm0:shared-entries")
    indexExpression (natural index) _ [.var "root", .var "claim"] initial 6 (by decide +kernel) counted last
  apply call_returns program bindings before after "mm0:shared-entries" _ _ (by decide +kernel) _ (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
    variable_prefix_arguments_return program bindings before after (.function "mm0:shared-entries")
      ["terms", "defs", "thms", "ctx", hypothesesName, "saved"] [indexExpression, .var "root", .var "claim"] [] 0 _
      (by simpa [ct, cd, cth, cc, ch, cs, initial] using rest)

private theorem next_returns (tables : Proof.Tables) (context : Context) (processed : List Entry)
    (entry : Entry) (remaining : List Entry) (root : ProofWitness) (claim actual : Preterm)
    (before after : State) (answer : Bool)
    (child : PureReturns program (environment (ProofStore.extend tables actual) context
      ((processed ++ [entry]) ++ remaining) (processed ++ [entry]).length root claim)
      before equation.body after (boolean answer)) :
    PureReturns program
      (("next", Proof.hypothesesValue (ProofStore.extend tables actual)) ::
        checkedEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry actual)
      before nextBody after (boolean answer) := by
  rw [next_shape]
  let bindings := ("next", Proof.hypothesesValue (ProofStore.extend tables actual)) ::
    checkedEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry actual
  have increment : PureReturns program bindings before (.expression [.symbol "+", .var "index", .grounded (.int 1)]) before (natural (processed.length + 1)) := by
    apply native_binary_call_returns program bindings before before before before "+" _ _ (natural processed.length) (.grounded (.int 1)) _
      (by decide) (by decide) (by decide) (by decide) _ (grounded_returns program bindings before (.int 1)) _ (by decide)
    · simpa [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup] using variable_returns program bindings before "index"
    · simp [StdLib.apply, natural]
  apply entries_call_returns (ProofStore.extend tables actual) context (processed ++ entry :: remaining)
    (processed.length + 1) root claim bindings "next" _ before after answer
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup, ProofStore.extend])
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup, ProofStore.extend])
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup, ProofStore.extend])
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup])
    rfl
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup])
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup])
    (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup])
    increment
  simpa [List.append_assoc] using child

private theorem answer_none_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (state : State) :
    PureReturns program (answerEnvironment tables context saved index root claim entry none)
      state answerBody state (boolean false) := by
  rw [answer_shape]
  let bindings := answerEnvironment tables context saved index root claim entry none
  apply case_returns program bindings bindings state state state (.var "answer") (.symbol "None")
    (boolean false) _ _ answerCases (read_cases_encoded _)
  · simpa [bindings, answerEnvironment, applySubst, Subst.lookup, ProofResults.resultValue, optionValue] using
      variable_returns program bindings state "answer"
  · simp [answer_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact grounded_returns program bindings state (.bool false)

private theorem answer_some_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (actual : Preterm)
    (before after : State) (answer : Bool)
    (checked : PureReturns program (checkedEnvironment tables context saved index root claim entry actual)
      before checkedBody after (boolean answer)) :
    PureReturns program (answerEnvironment tables context saved index root claim entry (some actual))
      before answerBody after (boolean answer) := by
  rw [answer_shape]
  let bindings := answerEnvironment tables context saved index root claim entry (some actual)
  apply case_returns program bindings (checkedEnvironment tables context saved index root claim entry actual)
    before before after (.var "answer") (ProofResults.resultValue (some actual)) checkedBody _ _ answerCases (read_cases_encoded _)
  · simpa [bindings, answerEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "answer"
  · simp [answer_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, Subst.lookup,
      ProofResults.resultValue, optionValue]
  · exact checked

private theorem expected_test_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (actual : Preterm) (state : State) :
    PureReturns program (checkedEnvironment tables context saved index root claim entry actual) state expectedGuard state
      (boolean (decide (entry.expected = none ∨ entry.expected = some actual))) := by
  apply expected_guard_returns
  · simp [checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup]
  · rfl
  · simp [checkedEnvironment, answerEnvironment, entryEnvironment, environment, Subst.lookup]

private theorem checked_refused_returns (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (index : Nat) (root : ProofWitness) (claim : Preterm) (entry : Entry) (actual : Preterm) (state : State)
    (wrong : ¬ (entry.expected = none ∨ entry.expected = some actual)) :
    PureReturns program (checkedEnvironment tables context saved index root claim entry actual)
      state checkedBody state (boolean false) := by
  rw [checked_shape]
  apply if_returns program _ state state state _ _ _ _ _ (expected_test_returns tables context saved index root claim entry actual state)
  simpa [wrong, boolean] using grounded_returns program
    (checkedEnvironment tables context saved index root claim entry actual) state (.bool false)

private theorem published_returns (tables : Proof.Tables) (context : Context) (processed : List Entry)
    (entry : Entry) (remaining : List Entry) (root : ProofWitness) (claim actual : Preterm)
    (before middle after : State) (answer : Bool)
    (published : ∀ bindings vectorName expressionName,
      applySubst bindings (.var vectorName) = Proof.hypothesesValue tables →
      applySubst bindings (.var expressionName) = Data.preterm actual →
      PureReturns program bindings before (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var expressionName]) middle
        (Proof.hypothesesValue (ProofStore.extend tables actual)))
    (child : PureReturns program (environment (ProofStore.extend tables actual) context
      ((processed ++ [entry]) ++ remaining) (processed ++ [entry]).length root claim)
      middle equation.body after (boolean answer)) :
    PureReturns program (checkedEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry actual)
      before publishBody after (boolean answer) := by
  rw [publish_shape]
  let bindings := checkedEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry actual
  let bound := ("next", Proof.hypothesesValue (ProofStore.extend tables actual)) :: bindings
  apply let_returns program bindings bound before middle after (.var "next") _ _ (Proof.hypothesesValue (ProofStore.extend tables actual)) _
  · exact published bindings "hyps" "actual" (by simp [bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, applySubst, Subst.lookup]) rfl
  · simp [SpaceSemantics.matchValue, matchAtom, bindings, checkedEnvironment, answerEnvironment, entryEnvironment, environment, Subst.lookup, bound]
  · exact next_returns tables context processed entry remaining root claim actual middle after answer child

private theorem checked_accepted_returns (tables : Proof.Tables) (context : Context) (processed : List Entry)
    (entry : Entry) (remaining : List Entry) (root : ProofWitness) (claim actual : Preterm)
    (before middle after : State) (answer : Bool)
    (expected : entry.expected = none ∨ entry.expected = some actual)
    (published : ∀ bindings vectorName expressionName,
      applySubst bindings (.var vectorName) = Proof.hypothesesValue tables →
      applySubst bindings (.var expressionName) = Data.preterm actual →
      PureReturns program bindings before (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var expressionName]) middle
        (Proof.hypothesesValue (ProofStore.extend tables actual)))
    (child : PureReturns program (environment (ProofStore.extend tables actual) context
      ((processed ++ [entry]) ++ remaining) (processed ++ [entry]).length root claim)
      middle equation.body after (boolean answer)) :
    PureReturns program (checkedEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry actual)
      before checkedBody after (boolean answer) := by
  rw [checked_shape]
  apply if_returns program _ before before after _ _ _ _ _
    (expected_test_returns tables context (processed ++ entry :: remaining) processed.length root claim entry actual before)
  simpa [expected, boolean] using published_returns tables context processed entry remaining root claim actual before middle after answer published child

private theorem loop_entry_returns (tables : Proof.Tables) (context : Context) (processed : List Entry)
    (entry : Entry) (remaining : List Entry) (root : ProofWitness) (claim : Preterm)
    (before middle after : State) (result : Option Preterm) (answer : Bool)
    (computed : Proof.Call tables context entry.witness before middle result)
    (continued : PureReturns program
      (answerEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry result)
      middle answerBody after (boolean answer)) :
    PureReturns program (environment tables context (processed ++ entry :: remaining) processed.length root claim)
      before loopBody after (boolean answer) := by
  rw [entry_shape]
  let bindings := environment tables context (processed ++ entry :: remaining) processed.length root claim
  let bound := entryEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry
  apply let_returns program bindings bound before before after
    (.expression [.symbol "MM0:Saved", .var "expected", .var "proof"]) _ _ (entryValue entry) _
  · apply native_variable_call_returns program bindings before before "index-atom" ["saved", "index"] _ (by decide) (by decide) _ (by decide)
    simp [bindings, environment, applySubst, Subst.lookup, StdLib.apply, natural]
  · simp [entryValue, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom,
      bindings, bound, entryEnvironment, environment, Subst.lookup]
  · rw [proof_shape]
    let withAnswer := answerEnvironment tables context (processed ++ entry :: remaining) processed.length root claim entry result
    apply let_returns program bound withAnswer before middle after (.var "answer") _ _ (ProofResults.resultValue result) _
    · exact computed bound "terms" "defs" "thms" "ctx" "hyps" "proof"
        (by simp [bound, entryEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, entryEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, entryEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, entryEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, entryEnvironment, environment, applySubst, Subst.lookup]) rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withAnswer, answerEnvironment,
        bound, entryEnvironment, environment, Subst.lookup]
    · exact continued

/-- All finite initializer lists follow the actual loop. Every prefix is read
from a dense vector and extended only after its initializer has checked.
Refusal may leave the already checked prefix in the private vector, but cannot
publish a declaration or alter any other table or session cell. -/
theorem loop_returns (tables : Proof.Tables) (context : Context) (processed remaining : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State)
    (ready : Proof.Ready tables before) (independent : ProofStore.Independent tables) :
    ∃ after values answer,
      PureReturns program (environment tables context (processed ++ remaining) processed.length root claim)
        before equation.body after (boolean answer) ∧
      Proof.Ready { tables with values := values } after ∧
      (Checked context root claim tables remaining ↔ answer = true) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  induction remaining generalizing tables processed before with
  | nil =>
      obtain ⟨after, _, checked, readyAfter, frame⟩ := Proof.check_returns tables context root claim before ready
      refine ⟨after, tables.values, ProofWitness.check (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values root claim, ?_, readyAfter, ?_, ?_, frame.cells⟩
      · rw [equation_shape]
        apply if_returns program _ before before after _ _ _ _ _
          (condition_returns tables context (processed ++ []) processed.length root claim before)
        simpa [boolean] using checked (environment tables context processed processed.length root claim)
          "terms" "defs" "thms" "ctx" "hyps" "root" "claim" rfl rfl rfl rfl rfl rfl rfl
      · exact (checked_nil_iff tables context root claim).trans (ProofWitness.check_iff _ _ _ _ _ _ _).symm
      · exact fun other notCache _ => frame.other other notCache
  | cons entry remaining ih =>
      obtain ⟨checkedState, _, computed, readyChecked, frame⟩ := Proof.returns tables context entry.witness before ready
      cases result : ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (Proof.theoremSignature tables.declarations) context tables.values entry.witness with
      | none =>
          refine ⟨checkedState, tables.values, false, ?_, readyChecked, ?_, ?_, frame.cells⟩
          · rw [equation_shape]
            apply if_returns program _ before before checkedState _ _ _ _ _
              (condition_returns tables context (processed ++ entry :: remaining) processed.length root claim before)
            have loop := loop_entry_returns tables context processed entry remaining root claim before checkedState checkedState none false
              (by simpa only [result] using computed)
              (answer_none_returns tables context (processed ++ entry :: remaining) processed.length root claim entry checkedState)
            simpa [boolean] using loop
          · simp [checked_cons_refused tables context root claim entry remaining result]
          · exact fun other notCache _ => frame.other other notCache
      | some actual =>
          by_cases expected : entry.expected = none ∨ entry.expected = some actual
          · obtain ⟨publishedState, published, readyPublished, othersPublished, cellsPublished⟩ :=
              ProofStore.publication_returns tables actual checkedState readyChecked independent
            obtain ⟨after, values, answer, child, readyAfter, justified, othersAfter, cellsAfter⟩ :=
              ih (ProofStore.extend tables actual) (processed ++ [entry]) publishedState readyPublished (independent.after_extend actual)
            refine ⟨after, values, answer, ?_, readyAfter, ?_, ?_, cellsAfter.trans (cellsPublished.trans frame.cells)⟩
            · rw [equation_shape]
              apply if_returns program _ before before after _ _ _ _ _
                (condition_returns tables context (processed ++ entry :: remaining) processed.length root claim before)
              have loop := loop_entry_returns tables context processed entry remaining root claim before checkedState after (some actual) answer
                (by simpa only [result] using computed)
                (answer_some_returns tables context (processed ++ entry :: remaining) processed.length root claim entry actual checkedState after answer
                  (checked_accepted_returns tables context processed entry remaining root claim actual checkedState publishedState after answer expected published child))
              simpa [boolean] using loop
            · simpa only [expected, true_and] using (checked_cons_iff tables context root claim entry remaining actual result).trans
                (and_congr_right fun _ => justified)
            · intro other notCache notProofs
              rw [othersAfter other notCache notProofs, othersPublished other notProofs, frame.other other notCache]
          · refine ⟨checkedState, tables.values, false, ?_, readyChecked, ?_, ?_, frame.cells⟩
            · rw [equation_shape]
              apply if_returns program _ before before checkedState _ _ _ _ _
                (condition_returns tables context (processed ++ entry :: remaining) processed.length root claim before)
              have loop := loop_entry_returns tables context processed entry remaining root claim before checkedState checkedState (some actual) false
                (by simpa only [result] using computed)
                (answer_some_returns tables context (processed ++ entry :: remaining) processed.length root claim entry actual checkedState checkedState false
                  (checked_refused_returns tables context (processed ++ entry :: remaining) processed.length root claim entry actual checkedState expected))
              simpa [boolean] using loop
            · simp [checked_cons_iff tables context root claim entry remaining actual result, expected]
            · exact fun other notCache _ => frame.other other notCache

private def sharedEquation : SpaceSemantics.Equation := serviceSource.program.equations[0]'(by decide)

private def sharedEnvironment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) : Subst :=
  [("claim", Data.preterm claim), ("root", Proof.witnessValue root), ("saved", .expression (saved.map entryValue)),
   ("hyps", ListSubstitution.expressionsValue tables.values), ("ctx", Data.context context),
   ("thms", tableValue tables.theorems), ("defs", tableValue tables.definitions), ("terms", tableValue tables.terms)]

private theorem shared_unique :
    program.equations.filter (fun e => e.head == "mm0:shared-proof") = [sharedEquation] := by decide

private theorem shared_formals : sharedEquation.arguments =
    [.var "terms", .var "defs", .var "thms", .var "ctx", .var "hyps",
     .expression [.symbol "MM0:L", .var "saved"], .var "root", .var "claim"] := by decide

private theorem shared_shape : sharedEquation.body =
    .expression [.symbol "let", .var "store", .expression [.symbol "mm0:vector", .var "hyps"],
      .expression [.symbol "mm0:shared-entries", .var "terms", .var "defs", .var "thms", .var "ctx",
        .var "store", .var "saved", .grounded (.int 0), .var "root", .var "claim"]] := by decide

private theorem shared_clause (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) :
    clauses program "mm0:shared-proof" [tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, ListSubstitution.expressionsValue tables.values,
      ListAccess.listValue (saved.map entryValue), Proof.witnessValue root, Data.preterm claim] =
      [.evaluate (sharedEnvironment tables context saved root claim) sharedEquation.body] := by
  rw [clauses_use_only_the_named_equations, shared_unique]
  simp [shared_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, sharedEnvironment, ListAccess.listValue]

def Call (tables : Proof.Tables) (context : Context) (saved : List Entry) (root : ProofWitness) (claim : Preterm)
    (before after : State) (answer : Bool) : Prop :=
  ∀ bindings tn dn thn cn hn sn rn qn,
    applySubst bindings (.var tn) = tableValue tables.terms →
    applySubst bindings (.var dn) = tableValue tables.definitions →
    applySubst bindings (.var thn) = tableValue tables.theorems →
    applySubst bindings (.var cn) = Data.context context →
    applySubst bindings (.var hn) = ListSubstitution.expressionsValue tables.values →
    applySubst bindings (.var sn) = ListAccess.listValue (saved.map entryValue) →
    applySubst bindings (.var rn) = Proof.witnessValue root →
    applySubst bindings (.var qn) = Data.preterm claim →
    PureReturns program bindings before (.expression [.symbol "mm0:shared-proof", .var tn,
      .var dn, .var thn, .var cn, .var hn, .var sn, .var rn, .var qn]) after (boolean answer)

/-- The public shared-proof function clears prior two-field rows before
loading the original hypotheses. Admission must establish the frozen tables
and scoped cache; it need not assume the proof store is already correct. -/
theorem returns (tables : Proof.Tables) (context : Context) (saved : List Entry) (root : ProofWitness)
    (claim : Preterm) (before : State) (stored : List Atom)
    (termRows : before.read tables.terms = some (TableAccess.declarationRows tables.entries))
    (definitionRows : before.read tables.definitions = some (Unfolding.definitionRows tables.bodies))
    (theoremRows : before.read tables.theorems = some (Proof.theoremRows tables.declarations))
    (cache : InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache before)
    (current : before.cells "mm0-proof-store" = some (Effects.handleValue tables.hypotheses))
    (allocated : before.read tables.hypotheses = some stored)
    (shaped : Effects.RowsHaveArity 2 stored) (independent : ProofStore.Independent tables) :
    ∃ after values answer,
      Call tables context saved root claim before after answer ∧
      Proof.Ready { tables with values := values } after ∧
      (Checked context root claim tables saved ↔ answer = true) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  let bindings := sharedEnvironment tables context saved root claim
  obtain ⟨middle, initialized, represented, othersInitialized, cellsInitialized⟩ :=
    VectorInitialization.vector_captured_returns bindings before tables.hypotheses stored (tables.values.map Data.preterm) "hyps" rfl current allocated shaped
  have ready : Proof.Ready tables middle := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [othersInitialized tables.terms independent.terms]; exact termRows
    · rw [othersInitialized tables.definitions independent.definitions]; exact definitionRows
    · rw [othersInitialized tables.theorems independent.theorems]; exact theoremRows
    · rw [independent.vector]
      exact .vector represented
    · unfold InferenceCache.Ready
      rw [cellsInitialized, othersInitialized tables.cache (Ne.symm tables.separateHypotheses)]
      exact cache
  obtain ⟨after, values, answer, loop, readyAfter, justified, othersAfter, cellsAfter⟩ :=
    loop_returns tables context [] saved root claim middle ready independent
  have body : PureReturns program bindings before sharedEquation.body after (boolean answer) := by
    rw [shared_shape]
    let bound := ("store", Proof.hypothesesValue tables) :: bindings
    apply let_returns program bindings bound before middle after (.var "store") _ _ (Proof.hypothesesValue tables) _
    · simpa only [Proof.hypothesesValue_vector tables independent.vector, List.length_map] using initialized
    · simp [SpaceSemantics.matchValue, matchAtom, bindings, bound, sharedEnvironment, Subst.lookup]
    · apply entries_call_returns tables context saved 0 root claim bound "store" _ middle after answer
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup]) rfl
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, sharedEnvironment, applySubst, Subst.lookup])
        (grounded_returns program bound middle (.int 0))
      simpa only [List.nil_append, List.length_nil] using loop
  refine ⟨after, values, answer, ?_, readyAfter, justified, ?_, cellsAfter.trans cellsInitialized⟩
  · intro caller tn dn thn cn hn sn rn qn ct cd cth cc ch cs cr cq
    apply authored_variable_call_returns program caller bindings before after "mm0:shared-proof"
      [tn, dn, thn, cn, hn, sn, rn, qn] sharedEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
    simpa [ct, cd, cth, cc, ch, cs, cr, cq] using shared_clause tables context saved root claim
  · intro other notCache notProofs
    rw [othersAfter other notCache notProofs, othersInitialized other notProofs]

private def requestEnvironment (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) : Subst :=
  ("saved", ListAccess.listValue (saved.map entryValue)) :: sharedEnvironment tables context saved root claim

def requestConfiguration (state : State) (tables : Proof.Tables) (context : Context)
    (saved : List Entry) (root : ProofWitness) (claim : Preterm) : Configuration :=
  { state, control := .evaluate (requestEnvironment tables context saved root claim)
      (.expression [.symbol "mm0:shared-proof", .var "terms", .var "defs", .var "thms", .var "ctx",
        .var "hyps", .var "saved", .var "root", .var "claim"]) }

/-- Declaration admission provides these frozen snapshots. The private proof
space retains the row shape established by allocation and publication; the
old values need not be correct for the new epoch. -/
structure Input (tables : Proof.Tables) (state : State) : Prop where
  terms : state.read tables.terms = some (TableAccess.declarationRows tables.entries)
  definitions : state.read tables.definitions = some (Unfolding.definitionRows tables.bodies)
  theorems : state.read tables.theorems = some (Proof.theoremRows tables.declarations)
  cache : InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache state
  current : state.cells "mm0-proof-store" = some (Effects.handleValue tables.hypotheses)
  allocated : ∃ stored, state.read tables.hypotheses = some stored ∧
    Effects.RowsHaveArity 2 stored
  independent : ProofStore.Independent tables

/-- Shared-proof input explicitly requires the vector layout through its
physical publication/separation evidence. -/
theorem Input.vector {tables : Proof.Tables} {state : State} (input : Input tables state) :
    tables.storage = .vector := input.independent.vector

/-- Prior vector publication supplies the reset layout. The old values are
arbitrary here: there is no assumption that they prove the new statement or
belong to its context. -/
theorem Input.of_published_rows (tables : Proof.Tables) (state : State)
    (entries : List (Nat × Atom))
    (terms : state.read tables.terms = some (TableAccess.declarationRows tables.entries))
    (definitions : state.read tables.definitions = some (Unfolding.definitionRows tables.bodies))
    (theorems : state.read tables.theorems = some (Proof.theoremRows tables.declarations))
    (cache : InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache state)
    (current : state.cells "mm0-proof-store" = some (Effects.handleValue tables.hypotheses))
    (published : Store.Represents state tables.hypotheses entries)
    (independent : ProofStore.Independent tables) : Input tables state :=
  ⟨terms, definitions, theorems, cache, current,
    ⟨Store.rows entries, published, Store.rows_have_arity entries⟩, independent⟩

/-- Both accepted and refused shared-proof checks return this representation,
so subsequent resets need no hypothesis about the previous Boolean result. -/
theorem Input.of_previous_check (tables : Proof.Tables) (state : State)
    (ready : Proof.Ready tables state)
    (current : state.cells "mm0-proof-store" = some (Effects.handleValue tables.hypotheses))
    (independent : ProofStore.Independent tables) : Input tables state :=
  Input.of_published_rows tables state (Store.enumerate (tables.values.map Data.preterm))
    ready.terms ready.definitions ready.theorems ready.cache current
      (ready.vector_hypotheses independent.vector) independent

theorem sufficient_fuel (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before) :
    ∃ after values answer fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before tables context saved root claim) =
        .complete after [boolean answer] [] []) ∧
      Proof.Ready { tables with values := values } after ∧
      (Checked context root claim tables saved ↔ answer = true) ∧
      (∀ other, other ≠ tables.cache → other ≠ tables.hypotheses → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨stored, allocated, shaped⟩ := input.allocated
  obtain ⟨after, values, answer, called, ready, justified, others, cells⟩ :=
    returns tables context saved root claim before stored input.terms input.definitions input.theorems
      input.cache input.current allocated shaped input.independent
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (requestEnvironment tables context saved root claim) before after _ _
    (called (requestEnvironment tables context saved root claim) "terms" "defs" "thms" "ctx" "hyps" "saved" "root" "claim"
      rfl rfl rfl rfl rfl rfl rfl rfl)
  exact ⟨after, values, answer, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed,
    ready, justified, others, cells⟩

theorem checked_iff_source_accepts (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before) :
    Checked context root claim tables saved ↔
      ∃ after fuel, run program fuel (requestConfiguration before tables context saved root claim) =
        .complete after [boolean true] [] [] := by
  obtain ⟨reference, _, answer, referenceFuel, completed, _, justified, _, _⟩ :=
    sufficient_fuel tables context saved root claim before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro checked
    exact ⟨reference, referenceFuel, by simpa only [justified.mp checked] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    apply justified.mpr
    simpa [boolean] using same.2.1

theorem refusal_iff_source_refuses (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before) :
    (¬ Checked context root claim tables saved) ↔
      ∃ after fuel, run program fuel (requestConfiguration before tables context saved root claim) =
        .complete after [boolean false] [] [] := by
  obtain ⟨reference, _, answer, referenceFuel, completed, _, justified, _, _⟩ :=
    sufficient_fuel tables context saved root claim before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro refused
    have falseAnswer : answer = false := Bool.eq_false_iff.mpr (fun trueAnswer => refused (justified.mpr trueAnswer))
    exact ⟨reference, referenceFuel, by simpa only [falseAnswer] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have falseAnswer : answer = false := by simpa [boolean] using same.2.1
    rw [justified, falseAnswer]
    decide

theorem checked_iff_gslt_path (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before) :
    Checked context root claim tables saved ↔
      ∃ after, (theory program).MultiStep (requestConfiguration before tables context saved root claim)
        (finished after [boolean true] [] []) := by
  rw [checked_iff_source_accepts tables context saved root claim before input]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

private theorem Checked.retains_prefix {tables : Proof.Tables} {context : Context} {root : ProofWitness} {claim : Preterm}
    {entries : List Entry} (checked : Checked context root claim tables entries)
    (original : List Preterm) (recorded : List (Preterm × ProofWitness))
    (authorized : ProofStore.Authorized tables context original recorded) :
    ∃ saved,
      Kernel.SavedWitnessesChecked (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context original (recorded ++ saved) ∧
      ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context (original ++ (recorded ++ saved).map Prod.fst) root claim ∧
      List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
        (entry.expected = none ∨ entry.expected = some pair.1)) entries saved := by
  induction checked generalizing original recorded with
  | root given =>
      refine ⟨[], ?_, ?_, .nil⟩
      · simpa only [List.append_nil] using authorized.initializers
      · simpa only [List.append_nil, ← authorized.values] using given
  | @save tables entry remaining actual given expected _ ih =>
      obtain ⟨saved, initializers, rootChecked, corresponding⟩ :=
        ih original (recorded ++ [(actual, entry.witness)]) (authorized.record given)
      refine ⟨(actual, entry.witness) :: saved, ?_, ?_, .cons ⟨rfl, expected⟩ corresponding⟩
      · simpa only [ProofStore.extend, List.append_assoc, List.cons_append, List.nil_append] using initializers
      · simpa only [ProofStore.extend, List.append_assoc, List.cons_append, List.nil_append] using rootChecked

/-- The accepted service retains the submitted initializer witnesses in
order. Its logical evidence is MM0's existing chronological sharing judgment,
without reconstructing an expanded proof tree. -/
theorem Checked.retains_witnesses {tables : Proof.Tables} {context : Context} {root : ProofWitness} {claim : Preterm}
    {entries : List Entry} (checked : Checked context root claim tables entries) :
    ∃ saved,
      Kernel.SavedWitnessesChecked (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values saved ∧
      ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context (tables.values ++ saved.map Prod.fst) root claim ∧
      List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
        (entry.expected = none ∨ entry.expected = some pair.1)) entries saved := by
  simpa only [List.nil_append] using checked.retains_prefix tables.values [] (ProofStore.authorized_empty tables context)

theorem source_acceptance_sound (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before after : State) (fuel : Nat) (input : Input tables before)
    (returned : run program fuel (requestConfiguration before tables context saved root claim) =
      .complete after [boolean true] [] []) :
    Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values claim :=
  ((checked_iff_source_accepts tables context saved root claim before input).mpr ⟨after, fuel, returned⟩).derives

/-- With no initializers, the same entry point checks the very same ordinary
supplied witness. Clearing a private store does not add a proof premise. -/
theorem ordinary_proof_iff_source_accepts (tables : Proof.Tables) (context : Context)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before) :
    ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values root claim ↔
      ∃ after fuel, run program fuel (requestConfiguration before tables context [] root claim) =
        .complete after [boolean true] [] [] :=
  (checked_nil_iff tables context root claim).symm.trans
    (checked_iff_source_accepts tables context [] root claim before input)

/-- An initializer cannot reference itself or a future vector entry. This
holds for every initial scope and every raw store discarded by initialization. -/
theorem out_of_prefix_initializer_refuses (tables : Proof.Tables) (context : Context)
    (expected : Option Preterm) (index : Nat) (remaining : List Entry) (root : ProofWitness) (claim : Preterm)
    (before : State) (input : Input tables before) (outside : tables.values.length ≤ index) :
    ∃ after fuel, run program fuel
      (requestConfiguration before tables context (⟨expected, .hyp index⟩ :: remaining) root claim) =
        .complete after [boolean false] [] [] := by
  apply (refusal_iff_source_refuses tables context _ root claim before input).mp
  apply checked_cons_refused
  simpa only [ProofWitness.proof?] using (List.getElem?_eq_none outside)

/-- No combination of local sharing and conversion can bootstrap a theorem
without an original hypothesis or an available theorem. -/
theorem no_logical_basis_refuses (tables : Proof.Tables) (context : Context) (saved : List Entry)
    (root : ProofWitness) (claim : Preterm) (before : State) (input : Input tables before)
    (noHypotheses : tables.values = []) (noTheorems : tables.declarations = []) :
    ∃ after fuel, run program fuel (requestConfiguration before tables context saved root claim) =
        .complete after [boolean false] [] [] := by
  apply (refusal_iff_source_refuses tables context saved root claim before input).mp
  intro checked
  apply Kernel.no_derivation_without_hypotheses_or_theorems (signatureOf tables.entries)
    (Unfolding.definitionSignature tables.bodies) context claim
  have emptySignature : Proof.theoremSignature tables.declarations = (fun _ => none) := by
    rw [noTheorems]
    rfl
  simpa only [emptySignature, noHypotheses] using checked.derives

end Mettapedia.Languages.MM0.MeTTa.Sharing
