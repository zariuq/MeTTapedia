import Mettapedia.Languages.MM0.MeTTa.Data.Data
import Mettapedia.Languages.MM0.MeTTa.Data.Scalar
import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Indexed substitution entries in the retained MM0 source

The source pairs binders and expressions in their original order and numbers
them with unbounded naturals. Pairing truncates on unequal lists; arity is
checked separately before these entries are used for admissibility.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SubstitutionEntries

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (listValue viewValue)

def entryValue (entry : Kernel.Substitution.Entry) : Atom :=
  .expression [.symbol "MM0:Entry", Data.binder entry.1.1, Data.preterm entry.1.2, natural entry.2]

def entriesValue (entries : List Kernel.Substitution.Entry) : Atom :=
  listValue (entries.map entryValue)

private def expressionsValue (expressions : List Preterm) : Atom := listValue (expressions.map Data.preterm)
private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 46)[45]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 47)[46]'(by decide)
private def environment (formal : Context) (expressions : List Preterm) (index : Nat) : Subst :=
  [("index", natural index), ("expressions", expressionsValue expressions), ("formal", Data.context formal)]
private def viewEnvironment (formal : Context) (expressions : List Preterm) (index : Nat) : Subst :=
  [("index", natural index), ("expressionsInput", viewValue (expressions.map Data.preterm)),
    ("valueInput", viewValue (formal.map Data.binder))]
private def cases : SpaceSemantics.Cases :=
  match viewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def nonemptyBody : Atom := (cases[2]'(by decide)).2
private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:entries") = [equation] := by decide
private theorem view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:entries-view") = [viewEquation] := by decide
private theorem formals : equation.arguments = [.var "formal", .var "expressions", .var "index"] := by decide
private theorem view_formals :
    viewEquation.arguments = [.var "valueInput", .var "expressionsInput", .var "index"] := by decide
private theorem body_shape :
    equation.body = .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "formal"],
      .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "expressions"],
        .expression [.symbol "mm0:entries-view", .var "view", .var "view2", .var "index"]]] := by decide
private theorem view_body_shape :
    viewEquation.body = .expression [.symbol "case", .expression [.var "valueInput", .var "expressionsInput"],
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem cases_shape :
    cases = [(.expression [.symbol "List:Nil", .var "expressions"], listValue []),
      (.expression [.expression [.symbol "List:Cons", .var "binder", .var "formal"], .symbol "List:Nil"], listValue []),
      (.expression [.expression [.symbol "List:Cons", .var "binder", .var "formal"],
        .expression [.symbol "List:Cons", .var "expression", .var "expressions"]], nonemptyBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem nonempty_body_shape :
    nonemptyBody = .expression [.symbol "let", .var "entry",
      .expression [.symbol "MM0:Entry", .var "binder", .var "expression", .var "index"],
      .expression [.symbol "let", .var "entriesResult",
        .expression [.symbol "let", .var "natAddResult",
          .expression [.symbol "mm0:nat-add", .var "index", natural 1],
          .expression [.symbol "mm0:entries", .var "formal", .var "expressions", .var "natAddResult"]],
        .expression [.symbol "mm0:list-cons", .var "entry", .var "entriesResult"]]] := by decide

private theorem clause (formal : Context) (expressions : List Preterm) (index : Nat) :
    clauses program "mm0:entries" [Data.context formal, expressionsValue expressions, natural index] =
      [.evaluate (environment formal expressions index) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (formal : Context) (expressions : List Preterm) (index : Nat) :
    clauses program "mm0:entries-view"
      [viewValue (formal.map Data.binder), viewValue (expressions.map Data.preterm), natural index] =
      [.evaluate (viewEnvironment formal expressions index) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]

private theorem call_from_body (bindings : Subst) (state : State) (formal : Context)
    (expressions : List Preterm) (index : Nat) (formalName expressionsName indexName : String)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedExpressions : applySubst bindings (.var expressionsName) = expressionsValue expressions)
    (capturedIndex : applySubst bindings (.var indexName) = natural index)
    (computed : PureReturns program (environment formal expressions index) state equation.body state
      (entriesValue ((formal.zip expressions).zipIdx index))) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:entries", .var formalName, .var expressionsName, .var indexName]) state
      (entriesValue ((formal.zip expressions).zipIdx index)) := by
  apply authored_variable_call_returns program bindings (environment formal expressions index) state state
    "mm0:entries" [formalName, expressionsName, indexName] equation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedFormal, capturedExpressions, capturedIndex] using clause formal expressions index

private theorem body_from_view (state : State) (formal : Context) (expressions : List Preterm) (index : Nat)
    (computed : PureReturns program (viewEnvironment formal expressions index) state viewEquation.body state
      (entriesValue ((formal.zip expressions).zipIdx index))) :
    PureReturns program (environment formal expressions index) state equation.body state
      (entriesValue ((formal.zip expressions).zipIdx index)) := by
  rw [body_shape]
  let bindings := environment formal expressions index
  let viewed := ("view", viewValue (formal.map Data.binder)) :: bindings
  let both := ("view2", viewValue (expressions.map Data.preterm)) :: viewed
  apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue (formal.map Data.binder)) _
  · exact ListAccess.view_captured_returns bindings state "formal" (formal.map Data.binder) (by rfl)
  · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
  · apply let_returns program viewed both state state state (.var "view2") _ _ (viewValue (expressions.map Data.preterm)) _
    · exact ListAccess.view_captured_returns viewed state "expressions" (expressions.map Data.preterm) (by rfl)
    · simp [SpaceSemantics.matchValue, matchAtom, both, viewed, bindings, environment, Subst.lookup]
    · apply authored_variable_call_returns program both (viewEnvironment formal expressions index) state state
        "mm0:entries-view" ["view", "view2", "index"] viewEquation.body _
        (by decide) (by decide) (by decide) _ computed (by decide)
      simpa [both, viewed, bindings, environment, applySubst, Subst.lookup] using view_clause formal expressions index

theorem body_returns (state : State) (formal : Context) (expressions : List Preterm) (index : Nat) :
    PureReturns program (environment formal expressions index) state equation.body state
      (entriesValue ((formal.zip expressions).zipIdx index)) := by
  induction formal generalizing expressions index with
  | nil =>
      apply body_from_view state [] expressions index
      let bindings := viewEnvironment [] expressions index
      let bound := ("expressions", viewValue (expressions.map Data.preterm)) :: bindings
      rw [view_body_shape]
      apply case_returns program bindings bound state state state _
        (.expression [viewValue [], viewValue (expressions.map Data.preterm)]) (listValue []) _ _ cases (read_cases_encoded cases)
      · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "expressionsInput"]
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, bound, bindings, viewEnvironment, Subst.lookup]
      · exact empty_constructor_returns program bound state "MM0:L" list_is_data_constructor (by decide)
  | cons binder formal ih =>
      apply body_from_view state (binder :: formal) expressions index
      cases expressions with
      | nil =>
          let bindings := viewEnvironment (binder :: formal) [] index
          let bound := ("formal", Data.context formal) :: ("binder", Data.binder binder) :: bindings
          rw [view_body_shape]
          apply case_returns program bindings bound state state state _
            (.expression [viewValue ((binder :: formal).map Data.binder), viewValue []]) (listValue [])
            _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "expressionsInput"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.context,
              bound, bindings, viewEnvironment, Subst.lookup]
          · exact empty_constructor_returns program bound state "MM0:L" list_is_data_constructor (by decide)
      | cons expression expressions =>
          let bindings := viewEnvironment (binder :: formal) (expression :: expressions) index
          let bound := ("expressions", expressionsValue expressions) :: ("expression", Data.preterm expression) ::
            ("formal", Data.context formal) :: ("binder", Data.binder binder) :: bindings
          rw [view_body_shape]
          apply case_returns program bindings bound state state state _
            (.expression [viewValue ((binder :: formal).map Data.binder), viewValue ((expression :: expressions).map Data.preterm)])
            nonemptyBody _ _ cases (read_cases_encoded cases)
          · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "expressionsInput"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.context, expressionsValue,
              bound, bindings, viewEnvironment, Subst.lookup]
          · rw [nonempty_body_shape]
            let entry := ((binder, expression), index)
            let paired := ("entry", entryValue entry) :: bound
            let rest := (formal.zip expressions).zipIdx (index + 1)
            let enumerated := ("entriesResult", entriesValue rest) :: paired
            apply let_returns program bound paired state state state (.var "entry") _ _ (entryValue entry) _
            · simpa [entry, entryValue, bound, bindings, viewEnvironment, applySubst, Subst.lookup] using
                constructor_variables_return program bound state "MM0:Entry" ["binder", "expression", "index"] (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, paired, entryValue, bound, bindings, viewEnvironment, Subst.lookup]
            · apply let_returns program paired enumerated state state state (.var "entriesResult") _ _ (entriesValue rest) _
              · let advanced := ("natAddResult", natural (index + 1)) :: paired
                apply let_returns program paired advanced state state state (.var "natAddResult") _ _ (natural (index + 1)) _
                · apply Scalar.addition_returns paired state index 1
                  · simpa [paired, bound, bindings, viewEnvironment, applySubst, Subst.lookup] using variable_returns program paired state "index"
                  · exact grounded_returns program paired state (.int 1)
                · simp [SpaceSemantics.matchValue, matchAtom, advanced, paired, bound, bindings, viewEnvironment, Subst.lookup]
                · exact call_from_body advanced state formal expressions (index + 1) "formal" "expressions" "natAddResult" rfl rfl rfl (ih expressions (index + 1))
              · simp [SpaceSemantics.matchValue, matchAtom, enumerated, paired, bound, bindings, viewEnvironment, Subst.lookup]
              · simpa [entry, rest, entriesValue, List.zipIdx_cons] using
                  ListAccess.cons_captured_returns enumerated state (entryValue entry) (rest.map entryValue) "entry" "entriesResult" rfl rfl

theorem captured_returns (bindings : Subst) (state : State) (formal : Context) (expressions : List Preterm) (index : Nat)
    (formalName expressionsName indexName : String)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedExpressions : applySubst bindings (.var expressionsName) = expressionsValue expressions)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:entries", .var formalName, .var expressionsName, .var indexName]) state
      (entriesValue ((formal.zip expressions).zipIdx index)) :=
  call_from_body bindings state formal expressions index formalName expressionsName indexName
    capturedFormal capturedExpressions capturedIndex (body_returns state formal expressions index)

theorem literal_index_captured_returns (bindings : Subst) (state : State) (formal : Context)
    (expressions : List Preterm) (index : Nat) (formalName expressionsName : String)
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedExpressions : applySubst bindings (.var expressionsName) = expressionsValue expressions) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:entries", .var formalName, .var expressionsName, natural index]) state
      (entriesValue ((formal.zip expressions).zipIdx index)) := by
  apply raw_call_returns program bindings state state "mm0:entries" _ _ (by decide) _ _ (by decide)
  · intro offset bounded
    have small : offset < 3 := by simpa using bounded
    have choices : offset = 0 ∨ offset = 1 ∨ offset = 2 := by omega
    rcases choices with same | same | same <;> subst offset <;> decide
  · have grounded : applySubst bindings (natural index) = natural index := by simp [natural, applySubst]
    simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, capturedFormal, capturedExpressions, grounded] using
      authored_function_arguments_return program bindings (environment formal expressions index) state state
        "mm0:entries" [Data.context formal, expressionsValue expressions, natural index] 3 equation.body _
        (by decide) (by decide) (clause formal expressions index) (body_returns state formal expressions index)

def requestConfiguration (state : State) (formal : Context) (expressions : List Preterm) (index : Nat) : Configuration :=
  { state, control := .evaluate (environment formal expressions index)
      (.expression [.symbol "mm0:entries", .var "formal", .var "expressions", .var "index"]) }

theorem sufficient_fuel (state : State) (formal : Context) (expressions : List Preterm) (index : Nat) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state formal expressions index) =
      .complete state [entriesValue ((formal.zip expressions).zipIdx index)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment formal expressions index) state state _ _
    (captured_returns _ state formal expressions index "formal" "expressions" "index" rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (state : State) (formal : Context) (expressions : List Preterm) (index : Nat) (answer : Atom) :
    answer = entriesValue ((formal.zip expressions).zipIdx index) ↔
      ∃ fuel, run program fuel (requestConfiguration state formal expressions index) = .complete state [answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state formal expressions index
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · rintro rfl; exact ⟨referenceFuel, reference⟩
  · rintro ⟨fuel, returned⟩
    exact (List.singleton_inj.mp (completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference returned).2.1).symm

theorem indices_do_not_wrap (state : State) :
    ∃ fuel, run program fuel (requestConfiguration state [.bound 0, .bound 0] [.var 1, .var 0] 18446744073709551615) =
      .complete state [entriesValue [((.bound 0, .var 1), 18446744073709551615), ((.bound 0, .var 0), 18446744073709551616)]] [] [] := by
  obtain ⟨fuel, completed⟩ := sufficient_fuel state [.bound 0, .bound 0] [.var 1, .var 0] 18446744073709551615
  exact ⟨fuel, by simpa using completed 0⟩

theorem truncation_is_not_arity_acceptance (state : State) :
    (∃ fuel, run program fuel (requestConfiguration state [.bound 0] [] 0) = .complete state [entriesValue []] [] []) ∧
      Kernel.Substitution.checkArguments (fun _ => none) [] [] [.bound 0] = false := by
  obtain ⟨fuel, completed⟩ := sufficient_fuel state [.bound 0] [] 0
  exact ⟨⟨fuel, by simpa using completed 0⟩, rfl⟩

end Mettapedia.Languages.MM0.MeTTa.SubstitutionEntries
