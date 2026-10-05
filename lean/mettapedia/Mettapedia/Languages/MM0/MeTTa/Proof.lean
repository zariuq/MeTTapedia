import Mettapedia.Languages.MM0.MeTTa.Conversion
import Mettapedia.Languages.MM0.MeTTa.TheoremInstantiation
import Mettapedia.Languages.MM0.MeTTa.ProofResults

/-!
# Supplied proofs in the retained MM0 source

Proof checking reads a frozen declaration snapshot and an ordered hypothesis
vector. Its only mutation is the scoped typing cache. The witness/list
correspondence follows the source's evaluation order, including absence that
stops before the remaining witness is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Proof

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State)
open NamedSpaces (Handle)
open Kernel (Context Preterm ProofWitness TheoremDecl TheoremInstance)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open ListSubstitution (expressionsValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open ProofResults (resultValue)

def witnessValue : ProofWitness → Atom
  | .hyp index => Hypothesis.witness index
  | .theoremApp index arguments children =>
      listValue [.symbol "MM0:TheoremApp", natural index, expressionsValue arguments,
        listValue (children.map witnessValue)]
  | .conversion witness child =>
      listValue [.symbol "MM0:Conversion", Conversion.witnessValue witness, witnessValue child]
termination_by witness => sizeOf witness

def theoremRows (entries : List (Nat × TheoremDecl)) : List Atom :=
  Store.rows (entries.map fun entry => (entry.1, TheoremInstantiation.declarationValue entry.2))

def theoremSignature (entries : List (Nat × TheoremDecl)) : Kernel.TheoremSignature :=
  fun index => (entries.find? fun entry => entry.1 = index).map Prod.snd

/-- Concrete tables used by this proof call. Admission establishes their
authorization separately; lookup never grants that authorization. -/
structure Tables where
  terms : Handle
  definitions : Handle
  theorems : Handle
  hypotheses : Handle
  cache : Handle
  entries : List ServiceInferenceCache.Row
  bodies : List (Nat × Kernel.Definition.Body)
  declarations : List (Nat × TheoremDecl)
  values : List Preterm
  uniqueTerms : ServiceInferenceCache.Unique entries
  uniqueDefinitions : ∀ key, (bodies.filter fun entry => entry.1 = key).length ≤ 1
  uniqueTheorems : ∀ key, (declarations.filter fun entry => entry.1 = key).length ≤ 1
  separateTerms : terms ≠ cache
  separateDefinitions : definitions ≠ cache
  separateTheorems : theorems ≠ cache
  separateHypotheses : hypotheses ≠ cache

def hypothesesValue (tables : Tables) : Atom :=
  VectorAccess.vectorValue tables.hypotheses tables.values.length

structure Ready (tables : Tables) (state : State) : Prop where
  terms : state.read tables.terms = some (declarationRows tables.entries)
  definitions : state.read tables.definitions = some (Unfolding.definitionRows tables.bodies)
  theorems : state.read tables.theorems = some (theoremRows tables.declarations)
  hypotheses : Store.Represents state tables.hypotheses (Store.enumerate (tables.values.map Data.preterm))
  cache : InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache state

theorem Ready.after_frame {tables : Tables} {before after : State} {bound : Nat}
    (ready : Ready tables before)
    (frame : InferenceCache.Frame tables.cache (tableValue tables.terms) bound before after)
    (cache : InferenceCache.Ready (signatureOf tables.entries) (tableValue tables.terms) tables.cache after) :
    Ready tables after := by
  refine ⟨?_, ?_, ?_, ?_, cache⟩
  · rw [frame.other tables.terms tables.separateTerms]; exact ready.terms
  · rw [frame.other tables.definitions tables.separateDefinitions]; exact ready.definitions
  · rw [frame.other tables.theorems tables.separateTheorems]; exact ready.theorems
  · change after.read tables.hypotheses = _
    rw [frame.other tables.hypotheses tables.separateHypotheses]; exact ready.hypotheses

def Call (tables : Tables) (context : Context) (witness : ProofWitness)
    (before after : State) (answer : Option Preterm) : Prop :=
  ∀ bindings termsName definitionsName theoremsName contextName hypothesesName witnessName,
    applySubst bindings (.var termsName) = tableValue tables.terms →
    applySubst bindings (.var definitionsName) = tableValue tables.definitions →
    applySubst bindings (.var theoremsName) = tableValue tables.theorems →
    applySubst bindings (.var contextName) = Data.context context →
    applySubst bindings (.var hypothesesName) = hypothesesValue tables →
    applySubst bindings (.var witnessName) = witnessValue witness →
    PureReturns program bindings before (.expression [.symbol "mm0:proof", .var termsName,
      .var definitionsName, .var theoremsName, .var contextName, .var hypothesesName, .var witnessName]) after (resultValue answer)

def ChildrenCall (tables : Tables) (context : Context) (children : List ProofWitness)
    (before after : State) (answer : Option (List Preterm)) : Prop :=
  ∀ bindings termsName definitionsName theoremsName contextName hypothesesName childrenName,
    applySubst bindings (.var termsName) = tableValue tables.terms →
    applySubst bindings (.var definitionsName) = tableValue tables.definitions →
    applySubst bindings (.var theoremsName) = tableValue tables.theorems →
    applySubst bindings (.var contextName) = Data.context context →
    applySubst bindings (.var hypothesesName) = hypothesesValue tables →
    applySubst bindings (.var childrenName) = listValue (children.map witnessValue) →
    PureReturns program bindings before (.expression [.symbol "mm0:proof-children", .var termsName,
      .var definitionsName, .var theoremsName, .var contextName, .var hypothesesName, .var childrenName]) after (ListSubstitution.resultValue answer)

private def equation : SourceProgram.Equation := proofEquation
private def childrenEquation : SourceProgram.Equation := (kernelSource.program.equations.take 10)[9]'(by decide)
private def declarationEquation : SourceProgram.Equation := (kernelSource.program.equations.take 3)[2]'(by decide)
private def instanceEquation : SourceProgram.Equation := (kernelSource.program.equations.take 4)[3]'(by decide)
private def convertedEquation : SourceProgram.Equation := (kernelSource.program.equations.take 7)[6]'(by decide)
private def viewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 11)[10]'(by decide)
private def childEquation : SourceProgram.Equation := (kernelSource.program.equations.take 12)[11]'(by decide)

private def baseEnvironment (tables : Tables) (context : Context) : Subst :=
  [("hypotheses", hypothesesValue tables), ("context", Data.context context),
    ("theorems", tableValue tables.theorems), ("definitions", tableValue tables.definitions), ("table", tableValue tables.terms)]
private def environment (tables : Tables) (context : Context) (witness : ProofWitness) : Subst :=
  ("witness", witnessValue witness) :: baseEnvironment tables context
private def childrenEnvironment (tables : Tables) (context : Context) (children : List ProofWitness) : Subst :=
  ("children", listValue (children.map witnessValue)) :: baseEnvironment tables context
private def declarationEnvironment (tables : Tables) (context : Context) (found : Option TheoremDecl)
    (arguments : List Preterm) (children : List ProofWitness) : Subst :=
  [("children", listValue (children.map witnessValue)), ("arguments", expressionsValue arguments)] ++
    baseEnvironment tables context ++ [("valueInput", optionValue (found.map TheoremInstantiation.declarationValue))]
private def instanceEnvironment (tables : Tables) (context : Context) (found : Option TheoremInstance) (children : List ProofWitness) : Subst :=
  childrenEnvironment tables context children ++ [("valueInput", TheoremInstantiation.instanceValue found)]
private def convertedEnvironment (tables : Tables) (context : Context) (found : Option Kernel.ConversionResult) (child : ProofWitness) : Subst :=
  ("child", witnessValue child) :: baseEnvironment tables context ++ [("valueInput", ConversionResults.resultValue found)]
private def viewEnvironment (tables : Tables) (context : Context) (children : List ProofWitness) : Subst :=
  baseEnvironment tables context ++ [("valueInput", viewValue (children.map witnessValue))]
private def childEnvironment (tables : Tables) (context : Context) (found : Option Preterm) (children : List ProofWitness) : Subst :=
  childrenEnvironment tables context children ++ [("valueInput", resultValue found)]

private def casesOf (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def cases := casesOf equation.body
private def declarationCases := casesOf declarationEquation.body
private def instanceCases := casesOf instanceEquation.body
private def convertedCases := casesOf convertedEquation.body
private def viewCases := casesOf viewEquation.body
private def childCases := casesOf childEquation.body
private def theoremBody : Atom := (cases[1]'(by decide)).2
private def conversionBody : Atom := (cases[2]'(by decide)).2
private def declarationBody : Atom := (declarationCases[1]'(by decide)).2
private def instanceBody : Atom := (instanceCases[1]'(by decide)).2
private def convertedBody : Atom := (convertedCases[1]'(by decide)).2
private def nilBody : Atom := (viewCases[0]'(by decide)).2
private def consBody : Atom := (viewCases[1]'(by decide)).2
private def childBody : Atom := (childCases[1]'(by decide)).2

private theorem unique : program.equations.filter (fun e => e.head == "mm0:proof") = [equation] := by decide
private theorem children_unique : program.equations.filter (fun e => e.head == "mm0:proof-children") = [childrenEquation] := by decide
private theorem declaration_unique : program.equations.filter (fun e => e.head == "mm0:proof-declaration") = [declarationEquation] := by decide
private theorem instance_unique : program.equations.filter (fun e => e.head == "mm0:proof-instance") = [instanceEquation] := by decide
private theorem converted_unique : program.equations.filter (fun e => e.head == "mm0:proof-converted") = [convertedEquation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:proof-children-view") = [viewEquation] := by decide
private theorem child_unique : program.equations.filter (fun e => e.head == "mm0:proof-child") = [childEquation] := by decide
private theorem formals : equation.arguments = [.var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "witness"] := by decide
private theorem children_formals : childrenEquation.arguments = [.var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"] := by decide
private theorem declaration_formals : declarationEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "arguments", .var "children"] := by decide
private theorem instance_formals : instanceEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"] := by decide
private theorem converted_formals : convertedEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "child"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses"] := by decide
private theorem child_formals : childEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"] := by decide

private theorem clause (tables : Tables) (context : Context) (witness : ProofWitness) :
    clauses program "mm0:proof" [tableValue tables.terms, tableValue tables.definitions, tableValue tables.theorems,
      Data.context context, hypothesesValue tables, witnessValue witness] = [.evaluate (environment tables context witness) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, environment, baseEnvironment]
private theorem children_clause (tables : Tables) (context : Context) (children : List ProofWitness) :
    clauses program "mm0:proof-children" [tableValue tables.terms, tableValue tables.definitions, tableValue tables.theorems,
      Data.context context, hypothesesValue tables, listValue (children.map witnessValue)] = [.evaluate (childrenEnvironment tables context children) childrenEquation.body] := by
  rw [clauses_use_only_the_named_equations, children_unique]
  simp [children_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, childrenEnvironment, baseEnvironment]
private theorem declaration_clause (tables : Tables) (context : Context) (found : Option TheoremDecl) (arguments : List Preterm) (children : List ProofWitness) :
    clauses program "mm0:proof-declaration" [optionValue (found.map TheoremInstantiation.declarationValue), tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, hypothesesValue tables, expressionsValue arguments, listValue (children.map witnessValue)] =
      [.evaluate (declarationEnvironment tables context found arguments children) declarationEquation.body] := by
  rw [clauses_use_only_the_named_equations, declaration_unique]
  simp [declaration_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, declarationEnvironment, baseEnvironment]
private theorem instance_clause (tables : Tables) (context : Context) (found : Option TheoremInstance) (children : List ProofWitness) :
    clauses program "mm0:proof-instance" [TheoremInstantiation.instanceValue found, tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, hypothesesValue tables, listValue (children.map witnessValue)] =
      [.evaluate (instanceEnvironment tables context found children) instanceEquation.body] := by
  rw [clauses_use_only_the_named_equations, instance_unique]
  simp [instance_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, instanceEnvironment, childrenEnvironment, baseEnvironment]
private theorem converted_clause (tables : Tables) (context : Context) (found : Option Kernel.ConversionResult) (child : ProofWitness) :
    clauses program "mm0:proof-converted" [ConversionResults.resultValue found, tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, hypothesesValue tables, witnessValue child] =
      [.evaluate (convertedEnvironment tables context found child) convertedEquation.body] := by
  rw [clauses_use_only_the_named_equations, converted_unique]
  simp [converted_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, convertedEnvironment, baseEnvironment]
private theorem view_clause (tables : Tables) (context : Context) (children : List ProofWitness) :
    clauses program "mm0:proof-children-view" [viewValue (children.map witnessValue), tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, hypothesesValue tables] =
      [.evaluate (viewEnvironment tables context children) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment, baseEnvironment]
private theorem child_clause (tables : Tables) (context : Context) (found : Option Preterm) (children : List ProofWitness) :
    clauses program "mm0:proof-child" [resultValue found, tableValue tables.terms, tableValue tables.definitions,
      tableValue tables.theorems, Data.context context, hypothesesValue tables, listValue (children.map witnessValue)] =
      [.evaluate (childEnvironment tables context found children) childEquation.body] := by
  rw [clauses_use_only_the_named_equations, child_unique]
  simp [child_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, childEnvironment, childrenEnvironment, baseEnvironment]

private theorem call_from_body (tables : Tables) (context : Context) (witness : ProofWitness) (before after : State) (answer : Option Preterm)
    (computed : PureReturns program (environment tables context witness) before equation.body after (resultValue answer)) :
    Call tables context witness before after answer := by
  intro bindings tn dn thn cn hn wn ct cd cth cc ch cw
  apply authored_variable_call_returns program bindings (environment tables context witness) before after "mm0:proof"
    [tn, dn, thn, cn, hn, wn] equation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [ct, cd, cth, cc, ch, cw] using clause tables context witness

private theorem children_call_from_body (tables : Tables) (context : Context) (children : List ProofWitness) (before after : State) (answer : Option (List Preterm))
    (computed : PureReturns program (childrenEnvironment tables context children) before childrenEquation.body after (ListSubstitution.resultValue answer)) :
    ChildrenCall tables context children before after answer := by
  intro bindings tn dn thn cn hn wn ct cd cth cc ch cw
  apply authored_variable_call_returns program bindings (childrenEnvironment tables context children) before after "mm0:proof-children"
    [tn, dn, thn, cn, hn, wn] childrenEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [ct, cd, cth, cc, ch, cw] using children_clause tables context children

theorem hypothesis_returns (tables : Tables) (context : Context) (index : Nat) (state : State) (ready : Ready tables state) :
    Call tables context (.hyp index) state state (tables.values[index]?) := by
  apply call_from_body
  simp only [environment, baseEnvironment, witnessValue]
  apply Hypothesis.proof_body_returns_from_read state (tableValue tables.terms) (tableValue tables.definitions)
    (tableValue tables.theorems) (Data.context context) (hypothesesValue tables) index (resultValue (tables.values[index]?))
  let bindings := ("index", natural index) :: environment tables context (.hyp index)
  have computed := VectorAccess.vector_returns bindings state tables.hypotheses
    (Store.rows (Store.enumerate (tables.values.map Data.preterm))) tables.values.length index "hypotheses" "index" ready.hypotheses rfl rfl
  by_cases bounded : index < tables.values.length
  · simpa [bindings, environment, baseEnvironment, witnessValue, bounded, List.length_map, Store.query_dense_prefix, List.getElem?_map, List.getElem?_eq_getElem bounded,
      VectorAccess.queryAnswer, resultValue, optionValue] using computed
  · simpa [bindings, environment, baseEnvironment, witnessValue, bounded, List.getElem?_eq_none (by omega : tables.values.length ≤ index), resultValue, optionValue] using computed

private theorem body_shape : equation.body = .expression [.symbol "case", .var "witness", .expression (cases.map fun e => .expression [e.1,e.2])] := by decide
private theorem cases_shape : cases =
    [(listValue [.symbol "MM0:Hyp", .var "index"], .expression [.symbol "mm0:data-at", .var "hypotheses", .var "index"]),
     (listValue [.symbol "MM0:TheoremApp", .var "index", .var "arguments", .var "children"], theoremBody),
     (listValue [.symbol "MM0:Conversion", .var "conversion", .var "child"], conversionBody),
     (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem theorem_body_shape : theoremBody =
    .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:nat-table-get", .var "theorems", .var "index"],
      .expression [.symbol "mm0:proof-declaration", .var "declaration", .var "table", .var "definitions", .var "theorems",
        .var "context", .var "hypotheses", .var "arguments", .var "children"]] := by decide
private theorem conversion_body_shape : conversionBody =
    .expression [.symbol "let", .var "converted", .expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "conversion"],
      .expression [.symbol "mm0:proof-converted", .var "converted", .var "table", .var "definitions", .var "theorems",
        .var "context", .var "hypotheses", .var "child"]] := by decide
private theorem converted_body_shape : convertedEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (convertedCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem converted_cases_shape : convertedCases =
    [(.symbol "None", .symbol "None"), (.expression [.symbol "MM0:Converted", .var "left", .var "right", .var "sort"], convertedBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem converted_some_shape : convertedBody =
    .expression [.symbol "let", .var "checked", .expression [.symbol "mm0:proof", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "child"],
      .expression [.symbol "mm0:proof-left", .var "checked", .var "left", .var "right"]] := by decide
private theorem child_body_shape : childEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (childCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem child_cases_shape : childCases =
    [(.symbol "None", .symbol "None"), (.expression [.symbol "Some", .var "first"], childBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem child_some_shape : childBody =
    .expression [.symbol "let", .var "checkedChildren", .expression [.symbol "mm0:proof-children", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"],
      .expression [.symbol "mm0:proof-tail", .var "checkedChildren", .var "first"]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (viewCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem view_cases_shape : viewCases =
    [(.symbol "List:Nil", nilBody), (.expression [.symbol "List:Cons", .var "child", .var "children"], consBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem nil_body_shape : nilBody =
    .expression [.symbol "let", .var "items", listValue [], .expression [.symbol "MM0:Expressions", .var "items"]] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "checked", .expression [.symbol "mm0:proof", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "child"],
      .expression [.symbol "mm0:proof-child", .var "checked", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"]] := by decide
private theorem children_body_shape : childrenEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "children"],
      .expression [.symbol "mm0:proof-children-view", .var "view", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses"]] := by decide

private theorem converted_none_body_returns (tables : Tables) (context : Context) (child : ProofWitness) (state : State) :
    PureReturns program (convertedEnvironment tables context none child) state convertedEquation.body state (.symbol "None") := by
  rw [converted_body_shape]
  let bindings := convertedEnvironment tables context none child
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ convertedCases (read_cases_encoded _)
  · simpa [bindings, convertedEnvironment, baseEnvironment, ConversionResults.resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [converted_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem converted_some_body_returns (tables : Tables) (context : Context) (converted : Kernel.ConversionResult) (child : ProofWitness)
    (before after : State) (answer : Option Preterm) (checked : Call tables context child before after answer) :
    PureReturns program (convertedEnvironment tables context (some converted) child) before convertedEquation.body after
      (resultValue (answer.bind fun expression => if expression = converted.left then some converted.right else none)) := by
  rw [converted_body_shape]
  let bindings := convertedEnvironment tables context (some converted) child
  let bound := ("sort", natural converted.sort) :: ("right", Data.preterm converted.right) :: ("left", Data.preterm converted.left) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (ConversionResults.resultValue (some converted)) convertedBody _ _ convertedCases (read_cases_encoded _)
  · simpa [bindings, convertedEnvironment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [converted_cases_shape, ConversionResults.resultValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, convertedEnvironment, baseEnvironment, Subst.lookup]
  · rw [converted_some_shape]
    let withResult := ("checked", resultValue answer) :: bound
    apply let_returns program bound withResult before after after (.var "checked") _ _ (resultValue answer) _
    · exact checked bound "table" "definitions" "theorems" "context" "hypotheses" "child" rfl rfl rfl rfl rfl rfl
    · dsimp only [withResult, bound, bindings, convertedEnvironment, childEnvironment, childrenEnvironment, viewEnvironment, environment, baseEnvironment]
      simp [SourceProgram.matchValue, matchAtom, Subst.lookup]
    · exact ProofResults.left_captured_returns withResult after answer converted.left converted.right "checked" "left" "right" rfl rfl rfl

private theorem converted_captured_returns (tables : Tables) (context : Context) (converted : Option Kernel.ConversionResult) (child : ProofWitness)
    (bindings : Subst) (before after : State) (answer : Option Preterm)
    (captured : applySubst bindings (.var "converted") = ConversionResults.resultValue converted)
    (ct : applySubst bindings (.var "table") = tableValue tables.terms)
    (cd : applySubst bindings (.var "definitions") = tableValue tables.definitions)
    (cth : applySubst bindings (.var "theorems") = tableValue tables.theorems)
    (cc : applySubst bindings (.var "context") = Data.context context)
    (ch : applySubst bindings (.var "hypotheses") = hypothesesValue tables)
    (cw : applySubst bindings (.var "child") = witnessValue child)
    (computed : PureReturns program (convertedEnvironment tables context converted child) before convertedEquation.body after (resultValue answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:proof-converted", .var "converted", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "child"]) after (resultValue answer) := by
  apply authored_variable_call_returns program bindings (convertedEnvironment tables context converted child) before after "mm0:proof-converted"
    ["converted", "table", "definitions", "theorems", "context", "hypotheses", "child"] convertedEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [captured, ct, cd, cth, cc, ch, cw] using converted_clause tables context converted child

private theorem child_none_body_returns (tables : Tables) (context : Context) (children : List ProofWitness) (state : State) :
    PureReturns program (childEnvironment tables context none children) state childEquation.body state (.symbol "None") := by
  rw [child_body_shape]
  let bindings := childEnvironment tables context none children
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ childCases (read_cases_encoded _)
  · simpa [bindings, childEnvironment, childrenEnvironment, baseEnvironment, resultValue, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [child_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem child_some_body_returns (tables : Tables) (context : Context) (first : Preterm) (children : List ProofWitness)
    (before after : State) (answer : Option (List Preterm)) (checked : ChildrenCall tables context children before after answer) :
    PureReturns program (childEnvironment tables context (some first) children) before childEquation.body after
      (ListSubstitution.resultValue (answer.map (first :: ·))) := by
  rw [child_body_shape]
  let bindings := childEnvironment tables context (some first) children
  let bound := ("first", Data.preterm first) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (resultValue (some first)) childBody _ _ childCases (read_cases_encoded _)
  · simpa [bindings, childEnvironment, childrenEnvironment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [child_cases_shape, resultValue, optionValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, childEnvironment, childrenEnvironment, baseEnvironment, Subst.lookup]
  · rw [child_some_shape]
    let withResult := ("checkedChildren", ListSubstitution.resultValue answer) :: bound
    apply let_returns program bound withResult before after after (.var "checkedChildren") _ _ (ListSubstitution.resultValue answer) _
    · exact checked bound "table" "definitions" "theorems" "context" "hypotheses" "children" rfl rfl rfl rfl rfl rfl
    · dsimp only [withResult, bound, bindings, convertedEnvironment, childEnvironment, childrenEnvironment, viewEnvironment, environment, baseEnvironment]
      simp [SourceProgram.matchValue, matchAtom, Subst.lookup]
    · exact ProofResults.tail_captured_returns withResult after answer first "checkedChildren" "first" rfl rfl

private theorem child_captured_returns (tables : Tables) (context : Context) (first : Option Preterm) (children : List ProofWitness)
    (bindings : Subst) (before after : State) (answer : Option (List Preterm))
    (captured : applySubst bindings (.var "checked") = resultValue first)
    (ct : applySubst bindings (.var "table") = tableValue tables.terms)
    (cd : applySubst bindings (.var "definitions") = tableValue tables.definitions)
    (cth : applySubst bindings (.var "theorems") = tableValue tables.theorems)
    (cc : applySubst bindings (.var "context") = Data.context context)
    (ch : applySubst bindings (.var "hypotheses") = hypothesesValue tables)
    (cw : applySubst bindings (.var "children") = listValue (children.map witnessValue))
    (computed : PureReturns program (childEnvironment tables context first children) before childEquation.body after (ListSubstitution.resultValue answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:proof-child", .var "checked", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"]) after (ListSubstitution.resultValue answer) := by
  apply authored_variable_call_returns program bindings (childEnvironment tables context first children) before after "mm0:proof-child"
    ["checked", "table", "definitions", "theorems", "context", "hypotheses", "children"] childEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [captured, ct, cd, cth, cc, ch, cw] using child_clause tables context first children

private theorem view_nil_body_returns (tables : Tables) (context : Context) (state : State) :
    PureReturns program (viewEnvironment tables context []) state viewEquation.body state (ListSubstitution.resultValue (some [])) := by
  rw [view_body_shape]
  let bindings := viewEnvironment tables context []
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "List:Nil") nilBody _ _ viewCases (read_cases_encoded _)
  · simpa [bindings, viewEnvironment, baseEnvironment, viewValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [view_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · rw [nil_body_shape]
    let withItems := ("items", listValue []) :: bindings
    apply let_returns program bindings withItems state state state (.var "items") _ _ (listValue []) _
    · exact empty_constructor_returns program bindings state "MM0:L" list_is_data_constructor (by decide)
    · simp [SourceProgram.matchValue, matchAtom, withItems, bindings, viewEnvironment, baseEnvironment, Subst.lookup]
    · simpa [withItems, ListSubstitution.resultValue, expressionsValue, applySubst, Subst.lookup] using
        unary_constructor_returns program withItems state "MM0:Expressions" "items" (by decide +kernel) (by decide)

private theorem view_cons_body_returns (tables : Tables) (context : Context) (child : ProofWitness) (children : List ProofWitness)
    (before middle after : State) (first : Option Preterm) (answer : Option (List Preterm))
    (checked : Call tables context child before middle first)
    (remaining : PureReturns program (childEnvironment tables context first children) middle childEquation.body after (ListSubstitution.resultValue answer)) :
    PureReturns program (viewEnvironment tables context (child :: children)) before viewEquation.body after (ListSubstitution.resultValue answer) := by
  rw [view_body_shape]
  let bindings := viewEnvironment tables context (child :: children)
  let bound := ("children", listValue (children.map witnessValue)) :: ("child", witnessValue child) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (viewValue ((child :: children).map witnessValue)) consBody _ _ viewCases (read_cases_encoded _)
  · simpa [bindings, viewEnvironment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [view_cases_shape, viewValue, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, viewEnvironment, baseEnvironment, Subst.lookup]
  · rw [cons_body_shape]
    let withResult := ("checked", resultValue first) :: bound
    apply let_returns program bound withResult before middle after (.var "checked") _ _ (resultValue first) _
    · exact checked bound "table" "definitions" "theorems" "context" "hypotheses" "child" rfl rfl rfl rfl rfl rfl
    · dsimp only [withResult, bound, bindings, convertedEnvironment, childEnvironment, childrenEnvironment, viewEnvironment, environment, baseEnvironment]
      simp [SourceProgram.matchValue, matchAtom, Subst.lookup]
    · exact child_captured_returns tables context first children withResult middle after answer rfl rfl rfl rfl rfl rfl rfl remaining

private theorem children_from_view (tables : Tables) (context : Context) (children : List ProofWitness) (before after : State) (answer : Option (List Preterm))
    (computed : PureReturns program (viewEnvironment tables context children) before viewEquation.body after (ListSubstitution.resultValue answer)) :
    ChildrenCall tables context children before after answer := by
  apply children_call_from_body
  rw [children_body_shape]
  let bindings := childrenEnvironment tables context children
  let viewed := ("view", viewValue (children.map witnessValue)) :: bindings
  apply let_returns program bindings viewed before before after (.var "view") _ _ (viewValue (children.map witnessValue)) _
  · exact ListAccess.view_captured_returns bindings before "children" _ rfl
  · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, childrenEnvironment, baseEnvironment, Subst.lookup]
  · apply authored_variable_call_returns program viewed (viewEnvironment tables context children) before after "mm0:proof-children-view"
      ["view", "table", "definitions", "theorems", "context", "hypotheses"] viewEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
    simpa [viewed, bindings, childrenEnvironment, baseEnvironment, applySubst, Subst.lookup] using view_clause tables context children

private theorem conversion_body_returns (tables : Tables) (context : Context) (witness : Kernel.ConvWitness) (child : ProofWitness)
    (before middle after : State) (converted : Option Kernel.ConversionResult) (answer : Option Preterm)
    (checked : Conversion.Call (tableValue tables.terms) (tableValue tables.definitions) context witness before middle converted)
    (remaining : PureReturns program (convertedEnvironment tables context converted child) middle convertedEquation.body after (resultValue answer)) :
    Call tables context (.conversion witness child) before after answer := by
  apply call_from_body
  rw [body_shape]
  let bindings := environment tables context (.conversion witness child)
  let bound := ("child", witnessValue child) :: ("conversion", Conversion.witnessValue witness) :: bindings
  apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.conversion witness child)) conversionBody _ _ cases (read_cases_encoded _)
  · simpa [bindings, environment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
  · simp [cases_shape, witnessValue, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, environment, baseEnvironment, Subst.lookup]
  · rw [conversion_body_shape]
    let withResult := ("converted", ConversionResults.resultValue converted) :: bound
    apply let_returns program bound withResult before middle after (.var "converted") _ _ (ConversionResults.resultValue converted) _
    · exact checked bound "table" "definitions" "context" "conversion" rfl rfl rfl rfl
    · dsimp only [withResult, bound, bindings, convertedEnvironment, childEnvironment, childrenEnvironment, viewEnvironment, environment, baseEnvironment]
      simp [SourceProgram.matchValue, matchAtom, Subst.lookup]
    · exact converted_captured_returns tables context converted child withResult middle after answer rfl rfl rfl rfl rfl rfl rfl remaining

private theorem declaration_body_shape : declarationEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (declarationCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem declaration_cases_shape : declarationCases =
    [(.symbol "None", .symbol "None"), (.expression [.symbol "Some", .var "declaration"], declarationBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem declaration_some_shape : declarationBody =
    .expression [.symbol "let", .var "instance", .expression [.symbol "mm0:instantiate-theorem", .var "table", .var "context", .var "declaration", .var "arguments"],
      .expression [.symbol "mm0:proof-instance", .var "instance", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"]] := by decide
private theorem instance_body_shape : instanceEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (instanceCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem instance_cases_shape : instanceCases =
    [(.symbol "None", .symbol "None"), (.expression [.symbol "MM0:Instance", .var "premises", .var "conclusion"], instanceBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem instance_some_shape : instanceBody =
    .expression [.symbol "let", .var "checkedChildren", .expression [.symbol "mm0:proof-children", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"],
      .expression [.symbol "mm0:proof-premises", .var "checkedChildren", .var "premises", .var "conclusion"]] := by decide

private theorem instance_none_body_returns (tables : Tables) (context : Context) (children : List ProofWitness) (state : State) :
    PureReturns program (instanceEnvironment tables context none children) state instanceEquation.body state (.symbol "None") := by
  rw [instance_body_shape]
  let bindings := instanceEnvironment tables context none children
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ instanceCases (read_cases_encoded _)
  · simpa [bindings, instanceEnvironment, childrenEnvironment, baseEnvironment, TheoremInstantiation.instanceValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [instance_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem instance_some_body_returns (tables : Tables) (context : Context) (instantiation : TheoremInstance) (children : List ProofWitness)
    (before after : State) (answer : Option (List Preterm)) (checked : ChildrenCall tables context children before after answer) :
    PureReturns program (instanceEnvironment tables context (some instantiation) children) before instanceEquation.body after
      (resultValue (answer.bind fun actual => if actual = instantiation.hypotheses then some instantiation.conclusion else none)) := by
  rw [instance_body_shape]
  let bindings := instanceEnvironment tables context (some instantiation) children
  let bound := ("conclusion", Data.preterm instantiation.conclusion) :: ("premises", expressionsValue instantiation.hypotheses) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (TheoremInstantiation.instanceValue (some instantiation)) instanceBody _ _ instanceCases (read_cases_encoded _)
  · simpa [bindings, instanceEnvironment, childrenEnvironment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [instance_cases_shape, TheoremInstantiation.instanceValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, instanceEnvironment, childrenEnvironment, baseEnvironment, Subst.lookup]
  · rw [instance_some_shape]
    let withResult := ("checkedChildren", ListSubstitution.resultValue answer) :: bound
    apply let_returns program bound withResult before after after (.var "checkedChildren") _ _ (ListSubstitution.resultValue answer) _
    · exact checked bound "table" "definitions" "theorems" "context" "hypotheses" "children" rfl rfl rfl rfl rfl rfl
    · simp [SourceProgram.matchValue, matchAtom, withResult, bound, bindings, instanceEnvironment, childrenEnvironment, baseEnvironment, Subst.lookup]
    · exact ProofResults.premises_captured_returns withResult after answer instantiation.hypotheses instantiation.conclusion "checkedChildren" "premises" "conclusion" rfl rfl rfl

private theorem instance_captured_returns (tables : Tables) (context : Context) (instantiation : Option TheoremInstance) (children : List ProofWitness)
    (bindings : Subst) (before after : State) (answer : Option Preterm)
    (captured : applySubst bindings (.var "instance") = TheoremInstantiation.instanceValue instantiation)
    (ct : applySubst bindings (.var "table") = tableValue tables.terms)
    (cd : applySubst bindings (.var "definitions") = tableValue tables.definitions)
    (cth : applySubst bindings (.var "theorems") = tableValue tables.theorems)
    (cc : applySubst bindings (.var "context") = Data.context context)
    (ch : applySubst bindings (.var "hypotheses") = hypothesesValue tables)
    (cw : applySubst bindings (.var "children") = listValue (children.map witnessValue))
    (computed : PureReturns program (instanceEnvironment tables context instantiation children) before instanceEquation.body after (resultValue answer)) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:proof-instance", .var "instance", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "children"]) after (resultValue answer) := by
  apply authored_variable_call_returns program bindings (instanceEnvironment tables context instantiation children) before after "mm0:proof-instance"
    ["instance", "table", "definitions", "theorems", "context", "hypotheses", "children"] instanceEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [captured, ct, cd, cth, cc, ch, cw] using instance_clause tables context instantiation children

private theorem declaration_none_body_returns (tables : Tables) (context : Context) (arguments : List Preterm) (children : List ProofWitness) (state : State) :
    PureReturns program (declarationEnvironment tables context none arguments children) state declarationEquation.body state (.symbol "None") := by
  rw [declaration_body_shape]
  let bindings := declarationEnvironment tables context none arguments children
  apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ declarationCases (read_cases_encoded _)
  · simpa [bindings, declarationEnvironment, baseEnvironment, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  · simp [declaration_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem declaration_some_body_returns (tables : Tables) (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) (children : List ProofWitness)
    (before middle after : State) (instantiation : Option TheoremInstance) (answer : Option Preterm)
    (instantiated : ∀ bindings tn cn dn an,
      applySubst bindings (.var tn) = tableValue tables.terms → applySubst bindings (.var cn) = Data.context context →
      applySubst bindings (.var dn) = TheoremInstantiation.declarationValue declaration → applySubst bindings (.var an) = expressionsValue arguments →
      PureReturns program bindings before (.expression [.symbol "mm0:instantiate-theorem", .var tn, .var cn, .var dn, .var an]) middle (TheoremInstantiation.instanceValue instantiation))
    (remaining : PureReturns program (instanceEnvironment tables context instantiation children) middle instanceEquation.body after (resultValue answer)) :
    PureReturns program (declarationEnvironment tables context (some declaration) arguments children) before declarationEquation.body after (resultValue answer) := by
  rw [declaration_body_shape]
  let bindings := declarationEnvironment tables context (some declaration) arguments children
  let bound := ("declaration", TheoremInstantiation.declarationValue declaration) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput") (optionValue (some (TheoremInstantiation.declarationValue declaration))) declarationBody _ _ declarationCases (read_cases_encoded _)
  · simpa [bindings, declarationEnvironment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [declaration_cases_shape, optionValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, declarationEnvironment, baseEnvironment, Subst.lookup]
  · rw [declaration_some_shape]
    let withResult := ("instance", TheoremInstantiation.instanceValue instantiation) :: bound
    apply let_returns program bound withResult before middle after (.var "instance") _ _ (TheoremInstantiation.instanceValue instantiation) _
    · exact instantiated bound "table" "context" "declaration" "arguments" rfl rfl rfl rfl
    · simp [SourceProgram.matchValue, matchAtom, withResult, bound, bindings, declarationEnvironment, baseEnvironment, Subst.lookup]
    · exact instance_captured_returns tables context instantiation children withResult middle after answer rfl rfl rfl rfl rfl rfl rfl remaining

private theorem theorem_body_returns (tables : Tables) (context : Context) (index : Nat) (arguments : List Preterm) (children : List ProofWitness)
    (before after : State) (allocated : before.read tables.theorems = some (theoremRows tables.declarations)) (answer : Option Preterm)
    (remaining : PureReturns program (declarationEnvironment tables context (theoremSignature tables.declarations index) arguments children) before declarationEquation.body after (resultValue answer)) :
    Call tables context (.theoremApp index arguments children) before after answer := by
  apply call_from_body
  rw [body_shape]
  let bindings := environment tables context (.theoremApp index arguments children)
  let bound := ("children", listValue (children.map witnessValue)) :: ("arguments", expressionsValue arguments) :: ("index", natural index) :: bindings
  apply case_returns program bindings bound before before after (.var "witness") (witnessValue (.theoremApp index arguments children)) theoremBody _ _ cases (read_cases_encoded _)
  · simpa [bindings, environment, baseEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "witness"
  · simp [cases_shape, witnessValue, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, environment, baseEnvironment, Subst.lookup]
  · rw [theorem_body_shape]
    let found := theoremSignature tables.declarations index
    let located := ("declaration", optionValue (found.map TheoremInstantiation.declarationValue)) :: bound
    apply let_returns program bound located before before after (.var "declaration") _ _ (optionValue (found.map TheoremInstantiation.declarationValue)) _
    · simpa [found, theoremSignature, Option.map_map, Function.comp_def] using TableAccess.indexed_rows_returns
        TheoremInstantiation.declarationValue bound before tables.theorems tables.declarations index "theorems" "index" tables.uniqueTheorems allocated rfl rfl
    · simp [SourceProgram.matchValue, matchAtom, located, bound, bindings, environment, baseEnvironment, Subst.lookup]
    · apply authored_variable_call_returns program located (declarationEnvironment tables context found arguments children) before after "mm0:proof-declaration"
        ["declaration", "table", "definitions", "theorems", "context", "hypotheses", "arguments", "children"] declarationEquation.body _ (by decide) (by decide) (by decide) _ remaining (by decide)
      simpa [located, bound, bindings, environment, baseEnvironment, applySubst, Subst.lookup] using declaration_clause tables context found arguments children

mutual

/-- The supplied witness is checked by the actual source. The induction does
not expand saved proofs and discharges each recursive execution premise. -/
theorem returns (tables : Tables) (context : Context) (witness : ProofWitness) (before : State) (ready : Ready tables before) :
    ∃ after bound,
      Call tables context witness before after
        (ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (theoremSignature tables.declarations) context tables.values witness) ∧
      Ready tables after ∧ InferenceCache.Frame tables.cache (tableValue tables.terms) bound before after := by
  cases witness with
  | hyp index =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      simpa only [ProofWitness.proof?] using hypothesis_returns tables context index before ready
  | theoremApp index arguments children =>
      cases found : theoremSignature tables.declarations index with
      | none =>
          refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
          simpa [ProofWitness.proof?, found, resultValue, optionValue] using
            theorem_body_returns tables context index arguments children before before ready.theorems none
              (by simpa only [found, resultValue, optionValue, Option.map_none] using declaration_none_body_returns tables context arguments children before)
      | some declaration =>
          obtain ⟨middle, instantiated, cacheMiddle, firstFrame⟩ := TheoremInstantiation.returns tables.terms tables.cache tables.entries
            tables.uniqueTerms tables.separateTerms context declaration arguments before ready.terms ready.cache
          have readyMiddle := ready.after_frame firstFrame cacheMiddle
          cases formed : declaration.instantiate? (signatureOf tables.entries) context arguments with
          | none =>
              refine ⟨middle, sizeOf arguments, ?_, readyMiddle, firstFrame⟩
              simpa [ProofWitness.proof?, found, formed, resultValue, optionValue] using
                theorem_body_returns tables context index arguments children before middle ready.theorems none
                  (by simpa only [found] using (declaration_some_body_returns tables context declaration arguments children before middle middle none none
                    (by simpa only [formed] using instantiated)
                    (by simpa only [resultValue, optionValue, Option.map_none] using instance_none_body_returns tables context children middle)))
          | some instantiation =>
              obtain ⟨after, bound, checkedChildren, readyAfter, secondFrame⟩ := children_returns tables context children middle readyMiddle
              refine ⟨after, max (sizeOf arguments) bound, ?_, readyAfter,
                (firstFrame.weaken (Nat.le_max_left _ _)).trans (secondFrame.weaken (Nat.le_max_right _ _))⟩
              simpa [ProofWitness.proof?, found, formed] using
                theorem_body_returns tables context index arguments children before after ready.theorems
                  ((ProofWitness.children? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
                    (theoremSignature tables.declarations) context tables.values children).bind
                      fun actual => if actual = instantiation.hypotheses then some instantiation.conclusion else none)
                  (by simpa only [found] using (declaration_some_body_returns tables context declaration arguments children before middle after (some instantiation) _
                    (by simpa only [formed] using instantiated)
                    (instance_some_body_returns tables context instantiation children middle after _ checkedChildren)))
  | conversion witness child =>
      obtain ⟨middle, firstBound, converted, cacheMiddle, firstFrame⟩ := Conversion.returns tables.terms tables.definitions tables.cache tables.entries tables.bodies
        tables.uniqueTerms tables.uniqueDefinitions tables.separateTerms tables.separateDefinitions context witness before ready.terms ready.definitions ready.cache
      have readyMiddle := ready.after_frame firstFrame cacheMiddle
      cases convertedResult : Kernel.ConvWitness.conversion? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies) context witness with
      | none =>
          refine ⟨middle, firstBound, ?_, readyMiddle, firstFrame⟩
          simpa [ProofWitness.proof?, convertedResult, resultValue, optionValue] using
            conversion_body_returns tables context witness child before middle middle none none
              (by simpa only [convertedResult] using converted)
              (by simpa only [resultValue, optionValue, Option.map_none] using converted_none_body_returns tables context child middle)
      | some value =>
          obtain ⟨after, secondBound, checkedChild, readyAfter, secondFrame⟩ := returns tables context child middle readyMiddle
          refine ⟨after, max firstBound secondBound, ?_, readyAfter,
            (firstFrame.weaken (Nat.le_max_left _ _)).trans (secondFrame.weaken (Nat.le_max_right _ _))⟩
          simpa [ProofWitness.proof?, convertedResult] using
            conversion_body_returns tables context witness child before middle after (some value) _
              (by simpa only [convertedResult] using converted)
              (converted_some_body_returns tables context value child middle after _ checkedChild)
termination_by sizeOf witness

/-- Premises are consumed in order. An absent child stops before the remaining
list; successful children retain their repeated conclusions. -/
theorem children_returns (tables : Tables) (context : Context) (children : List ProofWitness) (before : State) (ready : Ready tables before) :
    ∃ after bound,
      ChildrenCall tables context children before after
        (ProofWitness.children? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (theoremSignature tables.declarations) context tables.values children) ∧
      Ready tables after ∧ InferenceCache.Frame tables.cache (tableValue tables.terms) bound before after := by
  cases children with
  | nil =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      simpa only [ProofWitness.children?] using children_from_view tables context [] before before (some []) (view_nil_body_returns tables context before)
  | cons child children =>
      obtain ⟨middle, firstBound, checkedChild, readyMiddle, firstFrame⟩ := returns tables context child before ready
      cases first : ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (theoremSignature tables.declarations) context tables.values child with
      | none =>
          refine ⟨middle, firstBound, ?_, readyMiddle, firstFrame⟩
          simpa [ProofWitness.children?, first] using children_from_view tables context (child :: children) before middle none
            (view_cons_body_returns tables context child children before middle middle none none (by simpa only [first] using checkedChild)
              (child_none_body_returns tables context children middle))
      | some expression =>
          obtain ⟨after, secondBound, checkedChildren, readyAfter, secondFrame⟩ := children_returns tables context children middle readyMiddle
          refine ⟨after, max firstBound secondBound, ?_, readyAfter,
            (firstFrame.weaken (Nat.le_max_left _ _)).trans (secondFrame.weaken (Nat.le_max_right _ _))⟩
          simpa [ProofWitness.children?, first, Option.map_eq_bind] using children_from_view tables context (child :: children) before after _
            (view_cons_body_returns tables context child children before middle after (some expression) _ (by simpa only [first] using checkedChild)
              (child_some_body_returns tables context expression children middle after _ checkedChildren))
termination_by sizeOf children

end

def requestConfiguration (state : State) (tables : Tables) (context : Context) (witness : ProofWitness) : Configuration :=
  { state, control := .evaluate (environment tables context witness)
      (.expression [.symbol "mm0:proof", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "witness"]) }

theorem sufficient_fuel (tables : Tables) (context : Context) (witness : ProofWitness) (state : State) (ready : Ready tables state) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state tables context witness) =
        .complete after [resultValue (ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (theoremSignature tables.declarations) context tables.values witness)] [] []) ∧
      Ready tables after ∧ InferenceCache.Frame tables.cache (tableValue tables.terms) bound state after := by
  obtain ⟨after, bound, path, readyAfter, frame⟩ := returns tables context witness state ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment tables context witness) state after _ _
    (path _ "table" "definitions" "theorems" "context" "hypotheses" "witness" rfl rfl rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (tables : Tables) (context : Context) (witness : ProofWitness) (state : State) (ready : Ready tables state) (answer : Option Preterm) :
    ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state tables context witness) = .complete after [resultValue answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := sufficient_fuel tables context witness state ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact ProofResults.resultValue_injective (List.singleton_inj.mp same.2.1)

theorem checks_iff_source_returns (tables : Tables) (context : Context) (witness : ProofWitness) (state : State) (ready : Ready tables state) (claim : Preterm) :
    ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim ↔
      ∃ after fuel, run program fuel (requestConfiguration state tables context witness) = .complete after [resultValue (some claim)] [] [] :=
  (ProofWitness.proof_eq_some_iff (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
    (theoremSignature tables.declarations) context tables.values witness claim).symm.trans
      (result_iff_source_returns tables context witness state ready (some claim))

theorem refusal_iff_source_returns_none (tables : Tables) (context : Context) (witness : ProofWitness) (state : State) (ready : Ready tables state) :
    (¬ ∃ claim, ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim) ↔
      ∃ after fuel, run program fuel (requestConfiguration state tables context witness) = .complete after [.symbol "None"] [] [] :=
  (ProofWitness.proof_none_iff (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
    (theoremSignature tables.declarations) context tables.values witness).symm.trans
      (result_iff_source_returns tables context witness state ready none)

theorem checks_iff_gslt_path (tables : Tables) (context : Context) (witness : ProofWitness) (state : State) (ready : Ready tables state) (claim : Preterm) :
    ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state tables context witness) (finished after [resultValue (some claim)] [] []) := by
  rw [checks_iff_source_returns tables context witness state ready claim]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

private def checkEquation : SourceProgram.Equation := (kernelSource.program.equations.take 2)[1]'(by decide)
private def checkEnvironment (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) : Subst :=
  ("claim", Data.preterm claim) :: ("proof", witnessValue witness) :: baseEnvironment tables context
private theorem check_unique : program.equations.filter (fun e => e.head == "mm0:check-proof") = [checkEquation] := by decide
private theorem check_formals : checkEquation.arguments =
    [.var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "proof", .var "claim"] := by decide
private theorem check_body_shape : checkEquation.body =
    .expression [.symbol "let", .var "checked", .expression [.symbol "mm0:proof", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "proof"],
      .expression [.symbol "let", .var "answer", .expression [.symbol "Some", .var "claim"],
        .expression [.symbol "mm0:data-eq", .var "checked", .var "answer"]]] := by decide
private theorem check_clause (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) :
    clauses program "mm0:check-proof" [tableValue tables.terms, tableValue tables.definitions, tableValue tables.theorems,
      Data.context context, hypothesesValue tables, witnessValue witness, Data.preterm claim] =
      [.evaluate (checkEnvironment tables context witness claim) checkEquation.body] := by
  rw [clauses_use_only_the_named_equations, check_unique]
  simp [check_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, checkEnvironment, baseEnvironment]

def CheckCall (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (before after : State) (answer : Bool) : Prop :=
  ∀ bindings tn dn thn cn hn wn claimName,
    applySubst bindings (.var tn) = tableValue tables.terms →
    applySubst bindings (.var dn) = tableValue tables.definitions →
    applySubst bindings (.var thn) = tableValue tables.theorems →
    applySubst bindings (.var cn) = Data.context context →
    applySubst bindings (.var hn) = hypothesesValue tables →
    applySubst bindings (.var wn) = witnessValue witness →
    applySubst bindings (.var claimName) = Data.preterm claim →
    PureReturns program bindings before (.expression [.symbol "mm0:check-proof", .var tn, .var dn, .var thn, .var cn, .var hn, .var wn, .var claimName]) after (SourcePrimitives.boolean answer)

private theorem check_body_returns (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm)
    (before after : State) (answer : Option Preterm) (checked : Call tables context witness before after answer) :
    PureReturns program (checkEnvironment tables context witness claim) before checkEquation.body after
      (SourcePrimitives.boolean (decide (answer = some claim))) := by
  rw [check_body_shape]
  let bindings := checkEnvironment tables context witness claim
  let withResult := ("checked", resultValue answer) :: bindings
  apply let_returns program bindings withResult before after after (.var "checked") _ _ (resultValue answer) _
  · exact checked bindings "table" "definitions" "theorems" "context" "hypotheses" "proof" rfl rfl rfl rfl rfl rfl
  · simp [SourceProgram.matchValue, matchAtom, withResult, bindings, checkEnvironment, baseEnvironment, Subst.lookup]
  · let withClaim := ("answer", resultValue (some claim)) :: withResult
    apply let_returns program withResult withClaim after after after (.var "answer") _ _ (resultValue (some claim)) _
    · simpa [resultValue, optionValue, withResult, bindings, checkEnvironment, baseEnvironment, applySubst, Subst.lookup] using
        unary_constructor_returns program withResult after "Some" "claim" (by decide +kernel) (by decide)
    · simp [SourceProgram.matchValue, matchAtom, withClaim, withResult, bindings, checkEnvironment, baseEnvironment, Subst.lookup]
    · simpa only [ProofResults.resultValue_injective.eq_iff] using Scalar.data_equality_captured_returns withClaim after
        (resultValue answer) (resultValue (some claim)) "checked" "answer" rfl rfl

theorem check_returns (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (before : State) (ready : Ready tables before) :
    ∃ after bound, CheckCall tables context witness claim before after
      (ProofWitness.check (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (theoremSignature tables.declarations) context tables.values witness claim) ∧
      Ready tables after ∧ InferenceCache.Frame tables.cache (tableValue tables.terms) bound before after := by
  obtain ⟨after, bound, checked, readyAfter, frame⟩ := returns tables context witness before ready
  refine ⟨after, bound, ?_, readyAfter, frame⟩
  intro bindings tn dn thn cn hn wn claimName ct cd cth cc ch cw cclaim
  apply authored_variable_call_returns program bindings (checkEnvironment tables context witness claim) before after "mm0:check-proof"
    [tn, dn, thn, cn, hn, wn, claimName] checkEquation.body _ (by decide) (by decide) (by decide) _
    (check_body_returns tables context witness claim before after _ checked) (by decide)
  simpa [ct, cd, cth, cc, ch, cw, cclaim] using check_clause tables context witness claim

def checkRequestConfiguration (state : State) (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) : Configuration :=
  { state, control := .evaluate (checkEnvironment tables context witness claim)
      (.expression [.symbol "mm0:check-proof", .var "table", .var "definitions", .var "theorems", .var "context", .var "hypotheses", .var "proof", .var "claim"]) }

theorem check_sufficient_fuel (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (state : State) (ready : Ready tables state) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (checkRequestConfiguration state tables context witness claim) =
        .complete after [SourcePrimitives.boolean (ProofWitness.check (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
          (theoremSignature tables.declarations) context tables.values witness claim)] [] []) ∧
      Ready tables after ∧ InferenceCache.Frame tables.cache (tableValue tables.terms) bound state after := by
  obtain ⟨after, bound, path, readyAfter, frame⟩ := check_returns tables context witness claim state ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (checkEnvironment tables context witness claim) state after _ _
    (path _ "table" "definitions" "theorems" "context" "hypotheses" "proof" "claim" rfl rfl rfl rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem check_result_iff_source_returns (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (state : State) (ready : Ready tables state) (answer : Bool) :
    ProofWitness.check (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim = answer ↔
      ∃ after fuel, run program fuel (checkRequestConfiguration state tables context witness claim) = .complete after [SourcePrimitives.boolean answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := check_sufficient_fuel tables context witness claim state ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same; exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    simpa [SourcePrimitives.boolean] using same.2.1

theorem checks_iff_source_accepts (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (state : State) (ready : Ready tables state) :
    ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim ↔
      ∃ after fuel, run program fuel (checkRequestConfiguration state tables context witness claim) = .complete after [SourcePrimitives.boolean true] [] [] :=
  (ProofWitness.check_iff (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
    (theoremSignature tables.declarations) context tables.values witness claim).symm.trans
      (check_result_iff_source_returns tables context witness claim state ready true)

theorem refusal_iff_source_refuses (tables : Tables) (context : Context) (witness : ProofWitness) (claim : Preterm) (state : State) (ready : Ready tables state) :
    (¬ ProofWitness.Checks (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (theoremSignature tables.declarations) context tables.values witness claim) ↔
      ∃ after fuel, run program fuel (checkRequestConfiguration state tables context witness claim) = .complete after [SourcePrimitives.boolean false] [] [] := by
  rw [← ProofWitness.check_iff]
  exact (Bool.eq_false_iff).symm.trans (check_result_iff_source_returns tables context witness claim state ready false)

end Mettapedia.Languages.MM0.MeTTa.Proof
