import Mettapedia.GSLT.LanguageDef.RestAwareChecker
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 8

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open WellSorted RestAwareTyping
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_schema_typing.metta"
    sha256 "c40fdf2157964f17f4a68c399a80e706c711eaf5b2a1991b54980bfdd493a994"

private def sharedSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_scoped_execution.metta"
    sha256 "01978e71dedad9a468f39fe1ec54f3acc6851a07ff62b34595e6e534c8fa71e4"

private def inheritedHeads : List String :=
  ["gslt:automata:binding", "gslt:rule:row-at",
   "gslt:premise:parameter-type", "gslt:premise:parameter-representation"]

private def inherited : SpaceSemantics.Program where
  equations := [sharedSource.program.equations[32]'(by decide +kernel),
    sharedSource.program.equations[65]'(by decide +kernel),
    sharedSource.program.equations[134]'(by decide +kernel),
    sharedSource.program.equations[135]'(by decide +kernel)]
  declarations := [sharedSource.program.declarations[32]'(by decide +kernel),
    sharedSource.program.declarations[65]'(by decide +kernel),
    sharedSource.program.declarations[134]'(by decide +kernel),
    sharedSource.program.declarations[135]'(by decide +kernel)]


private theorem inherited_equations_selected :
    inherited.equations = sharedSource.program.equations.filter (fun row => inheritedHeads.contains row.head) := by
  rfl

private theorem inherited_declarations_selected :
    inherited.declarations = sharedSource.program.declarations.filter (retainedCallDeclaration inheritedHeads.contains) := by
  decide +kernel

def library : BridgeKit.Library :=
  ⟨{equations := [], declarations := []}, inherited.append source.program, ["gslt:"]⟩

theorem checked : library.check = true := by decide +kernel

def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (library.runtime.equations.map (·.head)).contains head

def freeTerm (context : List (String × TypeExpr)) : Term :=
  encodeList (fun entry => .application "Binding" [.string entry.1,typeTerm entry.2]) context

def declarationsTerm (language : LanguageDef) : Term := encodeList typingDeclarationTerm language.terms

def sortsTerm (language : LanguageDef) : Term := encodeList (fun row => .string row.name) language.types

private theorem typeTerm_injective : Function.Injective typeTerm := by
  intro first second same
  simpa only [InferenceCettaWire.AuthoredRule.decodeType?_typeTerm, Option.some.injEq] using
    congrArg InferenceCettaWire.AuthoredRule.decodeType? same

private theorem beq_as_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (first second : α) :
    (first == second) = decide (first = second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]

private theorem typeTerm_eq_base (type : TypeExpr) (category : String) :
    (typeTerm type = .application "TBase" [.string category]) ↔ type = .base category := by
  constructor
  · intro same
    apply typeTerm_injective
    simpa only [typeTerm] using same
  · intro same
    subst type
    rfl

private theorem typeOption_injective : Function.Injective (encodeOption typeTerm) := by
  intro first second same
  cases first <;> cases second <;> simp_all [encodeOption,typeTerm_injective.eq_iff]

theorem nil_matches_encoded_list {α : Type} (element : α → Term)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (items : List α) :
    SpaceSemantics.matchValue bindings (.symbol "LNil") (encoded (encodeList element items)) =
      match items with
      | [] => some bindings
      | _ :: _ => none := by
  cases items <;> simp [SpaceSemantics.matchValue, encodeList, CettaWireAtom.encode,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

theorem symbol_matches_application (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (symbol head : String) (arguments : List Term) :
    SpaceSemantics.matchValue bindings (.symbol symbol) (encoded (.application head arguments)) = none := by
  change SpaceSemantics.matchValue bindings (.symbol symbol)
    (.expression (.symbol head :: CettaWireAtom.encodeMany arguments)) = none
  simp only [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

theorem symbol_matches_pattern (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (symbol : String) (pattern : Pattern) :
    SpaceSemantics.matchValue bindings (.symbol symbol) (encoded (encodePattern pattern)) = none := by
  cases pattern <;> simp only [encodePattern] <;> apply symbol_matches_application

theorem symbol_matches_kind (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (symbol : String) (kind : CollType) :
    SpaceSemantics.matchValue bindings (.symbol symbol)
      (encoded (InferenceCettaWire.encodeCollectionType kind)) = none := by
  cases kind <;> change SpaceSemantics.matchValue _ _ (.grounded (.string _)) = none <;>
    simp only [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads library.runtime program)

syntax "schema_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| schema_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in checked using $agreement; metta_eval [$facts,*] with checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        encodeList, encodeOption, freeTerm, declarationsTerm, sortsTerm, parameterTerm,
        nil_matches_encoded_list, symbol_matches_application, symbol_matches_pattern, symbol_matches_kind, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList,
        InferenceCettaWire.encodeBinder, InferenceCettaWire.encodeRest,
        InferenceCettaWire.encodeCollectionType, $extra,*]))

include agreement in
@[metta_head "gslt:automata:binding"]
theorem binding_returns (host : Effects.State) (name : String) : ∀ (context : List (String × TypeExpr)),
    PureReturns program [] host
      (apply "gslt:automata:binding" [encoded (.string name),encoded (freeTerm context)])
      host (encoded (encodeOption typeTerm (FreeTypeContext.ofList context name)))
  | [] => by schema_eval using (agreement) unfolding [FreeTypeContext.ofList]
  | (key,value) :: later => by
      have rest := binding_returns host name later
      by_cases same : name = key
      · subst key
        schema_eval using (agreement) [rest] unfolding [FreeTypeContext.ofList]
      · schema_eval using (agreement) [rest] unfolding [FreeTypeContext.ofList,same,Ne.symm same]

include agreement in
@[metta_head "gslt:rule:row-at"]
theorem row_returns (element : TypeExpr → Term) (host : Effects.State) :
    ∀ (values : List TypeExpr) (index : Nat),
    PureReturns program [] host
      (apply "gslt:rule:row-at" [number index,encoded (encodeList element values)])
      host (encoded (encodeOption element values[index]?))
  | [],index => by schema_eval using (agreement)
  | value :: later,0 => by schema_eval using (agreement)
  | value :: later,index + 1 => by
      have rest := row_returns element host later index
      schema_eval using (agreement) [rest]

include agreement in
@[metta_head "gslt:premise:parameter-type"]
theorem parameter_returns (host : Effects.State) (parameter : TermParam) :
    PureReturns program [] host
      (apply "gslt:premise:parameter-type" [encoded (parameterTerm parameter)])
      host (encoded (encodeOption typeTerm (parameterType? parameter))) := by
  cases parameter with
  | simple name type => schema_eval using (agreement) unfolding [parameterType?]
  | abstractionNamed binder name type =>
      cases type <;> schema_eval using (agreement) unfolding [parameterType?,typeTerm]
  | multiAbstractionNamed binders name type =>
      cases type with
      | arrow domain codomain =>
          cases domain <;> schema_eval using (agreement) unfolding [parameterType?,typeTerm]
      | base sort => schema_eval using (agreement) unfolding [parameterType?,typeTerm]
      | multiBinder body => schema_eval using (agreement) unfolding [parameterType?,typeTerm]
      | collection kind body => schema_eval using (agreement) unfolding [parameterType?,typeTerm]

include agreement in
@[metta_head "gslt:premise:parameter-representation"]
theorem representation_returns (host : Effects.State) (parameter : TermParam) (pattern : Pattern) :
    PureReturns program [] host
      (apply "gslt:premise:parameter-representation" [encoded (parameterTerm parameter),encoded (encodePattern pattern)])
      host (Effects.boolean (matchesParameterRepresentation? parameter pattern)) := by
  cases parameter with
  | simple name type => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
  | abstractionNamed binder name type =>
      cases pattern with
      | lambda binder body =>
          cases binder <;> schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | bvar _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | fvar _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | apply _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | multiLambda _ _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | subst _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | collection kind elements rest =>
          cases kind <;> schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
  | multiAbstractionNamed binders name type =>
      cases pattern with
      | multiLambda arity binders body =>
          cases binders <;> schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | bvar _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | fvar _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | apply _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | lambda _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | subst _ _ => schema_eval using (agreement) unfolding [matchesParameterRepresentation?]
      | collection kind elements rest =>
          cases kind <;> schema_eval using (agreement) unfolding [matchesParameterRepresentation?]

include agreement in
@[metta_head "gslt:premise:schema-extend"]
theorem extend_returns (host : Effects.State) (domain : TypeExpr) (bound : List TypeExpr) : ∀ (count : Nat),
    PureReturns program [] host
      (apply "gslt:premise:schema-extend" [encoded (typeTerm domain),number count,encoded (encodeList typeTerm bound)])
      host (encoded (encodeList typeTerm (List.replicate count domain ++ bound)))
  | 0 => by schema_eval using (agreement)
  | count + 1 => by
      have rest := extend_returns host domain bound count
      schema_eval using (agreement) [rest] unfolding [List.replicate_succ]

include agreement in
@[metta_head "gslt:premise:schema-rest"]
theorem rest_returns (host : Effects.State) (free : List (String × TypeExpr))
    (kind : CollType) (elementType : TypeExpr) (rest : Option String) :
    PureReturns program [] host
      (apply "gslt:premise:schema-rest"
        [encoded (freeTerm free),encoded (InferenceCettaWire.encodeCollectionType kind),
         encoded (typeTerm elementType),encoded (InferenceCettaWire.encodeRest rest)])
      host (Effects.boolean (checkRestHasType (FreeTypeContext.ofList free) kind elementType rest)) := by
  cases rest with
  | none => schema_eval using (agreement) unfolding [checkRestHasType]
  | some name =>
      have looked := binding_returns program agreement host name free
      have result_eq : Effects.boolean (checkRestHasType (FreeTypeContext.ofList free) kind elementType (some name)) =
          Effects.boolean (decide (encodeOption typeTerm (FreeTypeContext.ofList free name) =
            encodeOption typeTerm (some (.collection kind elementType)))) := by
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [checkRestHasType, beq_iff_eq, decide_eq_true_eq, typeOption_injective.eq_iff]
      rw [result_eq]
      schema_eval using (agreement) [looked] unfolding [typeTerm]

include agreement in
/-- Ordered schema arguments use genuine recursive checks at the types stored
in their corresponding parameter declarations. -/
theorem arguments_returns_of (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) :
    ∀ (arguments : List Pattern) (parameters : List TermParam),
    (∀ child ∈ arguments, ∀ expected,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodePattern child),encoded (typeTerm expected)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound child expected))) →
    PureReturns program [] host
      (apply "gslt:premise:schema-arguments" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodeList encodePattern arguments),
        encoded (encodeList parameterTerm parameters)])
      host (Effects.boolean (checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments parameters)) := by
  intro arguments
  induction arguments with
  | nil =>
      intro parameters children
      cases parameters <;> schema_eval using (agreement) unfolding [checkSchemaArguments]
  | cons argument arguments induction =>
      intro parameters children
      cases parameters with
      | nil => schema_eval using (agreement) unfolding [checkSchemaArguments]
      | cons parameter parameters =>
          have parameterResult := parameter_returns program agreement host parameter
          cases found : parameterType? parameter with
          | none =>
              rw [found] at parameterResult
              rw [checkSchemaArguments,found]
              schema_eval using (agreement) [parameterResult]
          | some expected =>
              rw [found] at parameterResult
              have represented := representation_returns program agreement host parameter argument
              have checked := children argument (List.mem_cons_self ..) expected
              have later := induction parameters (fun child member expected =>
                children child (List.mem_cons_of_mem argument member) expected)
              cases representation : matchesParameterRepresentation? parameter argument <;>
                rw [representation] at represented
              · schema_eval using (agreement) [parameterResult,represented] unfolding [checkSchemaArguments,found,representation]
              · cases result : checkSchemaHasType language (FreeTypeContext.ofList free) bound argument expected <;>
                  rw [result] at checked
                · schema_eval using (agreement) [parameterResult,represented,checked] unfolding [checkSchemaArguments,found,representation,result]
                · schema_eval using (agreement) [parameterResult,represented,checked,later] unfolding [checkSchemaArguments,found,representation,result]

include agreement in
theorem elements_returns_of (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (elementType : TypeExpr) :
    ∀ (elements : List Pattern),
    (∀ child ∈ elements, ∀ expected,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodePattern child),encoded (typeTerm expected)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound child expected))) →
    PureReturns program [] host
      (apply "gslt:premise:schema-elements" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodeList encodePattern elements),
        encoded (typeTerm elementType)])
      host (Effects.boolean (checkSchemaElements language (FreeTypeContext.ofList free) bound elements elementType)) := by
  intro elements
  induction elements with
  | nil => intro children; schema_eval using (agreement) unfolding [checkSchemaElements]
  | cons element elements induction =>
      intro children
      have checked := children element (List.mem_cons_self ..) elementType
      have later := induction (fun child member expected => children child (List.mem_cons_of_mem element member) expected)
      cases result : checkSchemaHasType language (FreeTypeContext.ofList free) bound element elementType <;>
        rw [result] at checked
      · schema_eval using (agreement) [checked] unfolding [checkSchemaElements,result]
      · schema_eval using (agreement) [checked,later] unfolding [checkSchemaElements,result]

#print axioms arguments_returns_of
#print axioms elements_returns_of

theorem base_comparison_returns (host : Effects.State)
    (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (expected : TypeExpr) (category : String)
    (left : Mettapedia.Languages.ProcessCalculi.MORK.applySubst caller (.var "expected") = encoded (typeTerm expected))
    (right : Mettapedia.Languages.ProcessCalculi.MORK.applySubst caller (.var "result") = encoded (typeTerm (.base category))) :
    PureReturns program caller host
      (apply "==" [.var "expected",.var "result"]) host (Effects.boolean (decide (expected = .base category))) := by
  simpa only [typeTerm_injective.eq_iff] using
    CettaWireAtom.equality_captured_returns program caller host (typeTerm expected) (typeTerm (.base category))
      "expected" "result" left right

syntax "constructor_eval" " using " "(" term ")" " [" term,* "]"
  " at_base " "(" term "," term ")" " unfolding" " [" term,* "]" : tactic
macro_rules
  | `(tactic| constructor_eval using ($agreement) [$facts,*] at_base($expected,$category) unfolding [$extra,*]) => do
    let simps ← extra.getElems.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    let conditionFact := facts.getElems[0]!
    `(tactic|
      (schema_eval using ($agreement) [$facts,*] unfolding [$extra,*]
       all_goals
         apply pure_if_returns _ _ _ _ (decide ($expected = TypeExpr.base $category)) _ _ _
         · apply base_comparison_returns
           all_goals simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
             Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
             Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, Library.bind,
             typeTerm,encoded,CettaWireAtom.encode,CettaWireAtom.encodeMany,$simps,*]
         · simp only [decide_true,decide_false,↓reduceIte,$simps,*]
           metta_eval [$facts,*] with checked in $agreement unfolding
             [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
              Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
              Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, Library.bind,
              encodeList,encodeOption,parameterTerm,typingDeclarationTerm,freeTerm,declarationsTerm,sortsTerm,
              typeTerm,InferenceCettaWire.encodeList,nil_matches_encoded_list,
              symbol_matches_application,symbol_matches_pattern,symbol_matches_kind,$extra,*]
           all_goals
             apply pure_if_returns
             · metta_capture_agreed $agreement from $conditionFact unfolding
                 [sortsTerm,declarationsTerm,freeTerm,encodeList,parameterTerm,typeTerm,
                  InferenceCettaWire.encodeList,InferenceCettaWire.encodeBinder,$extra,*]
             · simp only [decide_true,decide_false,Bool.false_eq_true,↓reduceIte,$simps,*]
               metta_eval [$facts,*] with checked in $agreement unfolding
                 [sortsTerm,declarationsTerm,freeTerm,encodeList,typingDeclarationTerm,
                  typeTerm,parameterTerm,$extra,*]))

include agreement in
theorem constructors_returns_of (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (label : String)
    (arguments : List Pattern) (expected : TypeExpr)
    (children : ∀ child ∈ arguments, ∀ type,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodePattern child),encoded (typeTerm type)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound child type))) :
    ∀ (remaining : List GrammarRule),
    PureReturns program [] host
      (apply "gslt:premise:schema-constructors" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (.string label),
        encoded (encodeList encodePattern arguments),encoded (typeTerm expected),
        encoded (encodeList typingDeclarationTerm remaining)])
      host (Effects.boolean (remaining.any fun row =>
        row.label == label && expected == .base row.category && !usesBareCollection? row &&
          checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments row.params)) := by
  intro remaining
  induction remaining with
  | nil => schema_eval using (agreement)
  | cons row remaining induction =>
      have checked := arguments_returns_of program agreement host language free bound arguments row.params children
      rcases row with ⟨actual,category,parameters,syntaxRows,evaluation,algebra,representation⟩
      cases representation with
      | wrapped =>
          by_cases labelSame : actual = label <;>
            by_cases typeSame : expected = .base category <;>
              cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments parameters <;>
                rw [result] at checked <;>
                have recurse := induction <;>
                simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                  unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                    typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result]
      | bare =>
          by_cases labelSame : actual = label
          · by_cases typeSame : expected = .base category
            · cases parameters with
              | nil =>
                  cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments [] <;>
                    rw [result] at checked <;>
                    have recurse := induction <;>
                    simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                    constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                      unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                        typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result]
              | cons parameter parameters =>
                  cases parameters with
                  | cons second later =>
                      cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments (parameter :: second :: later) <;>
                        rw [result] at checked <;>
                        have recurse := induction <;>
                        simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                        constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                          unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                            typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result]
                  | nil =>
                      cases parameter with
                      | simple name type =>
                          cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments [TermParam.simple name type] <;>
                            rw [result] at checked <;>
                            have recurse := induction <;>
                            simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                            cases type <;>
                              constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                                unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                                  typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result,typeTerm]
                      | abstractionNamed binder name type =>
                          cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments [.abstractionNamed binder name type] <;>
                            rw [result] at checked <;>
                            have recurse := induction <;>
                            simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                            constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                              unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                                typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result]
                      | multiAbstractionNamed binders name type =>
                          cases result : checkSchemaArguments language (FreeTypeContext.ofList free) bound arguments [.multiAbstractionNamed binders name type] <;>
                            rw [result] at checked <;>
                            have recurse := induction <;>
                            simp only [typeSame,beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse <;>
                            constructor_eval using (agreement) [checked,recurse] at_base(expected,category)
                              unfolding [List.any_cons,usesBareCollection?,GrammarRule.bareParams,
                                typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame,result]
            · have recurse := induction
              simp only [beq_as_decide,usesBareCollection?,GrammarRule.bareParams] at recurse
              constructor_eval using (agreement) [recurse] at_base(expected,category)
                unfolding [List.any_cons,typingDeclarationTerm,typeTerm_eq_base,beq_as_decide,labelSame,typeSame]
          · have recurse := induction
            simp only [beq_as_decide] at recurse
            constructor_eval using (agreement) [recurse] at_base(expected,category)
              unfolding [List.any_cons,typingDeclarationTerm,beq_as_decide,labelSame]

include agreement in
theorem substitutions_returns_of (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (body replacement : Pattern) (expected : TypeExpr)
    (bodyReturns : ∀ domain,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm (domain :: bound)),
          encoded (encodePattern body),encoded (typeTerm expected)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free)
          (domain :: bound) body expected)))
    (replacementReturns : ∀ domain,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm bound),
          encoded (encodePattern replacement),encoded (typeTerm domain)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free)
          bound replacement domain))) :
    ∀ (remaining : List TypeDecl),
    PureReturns program [] host
      (apply "gslt:premise:schema-substitutions" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodePattern body),
        encoded (encodePattern replacement),encoded (typeTerm expected),
        encoded (encodeList (fun row => .string row.name) remaining)])
      host (Effects.boolean (remaining.any fun row =>
        checkSchemaHasType language (FreeTypeContext.ofList free) (.base row.name :: bound) body expected &&
        checkSchemaHasType language (FreeTypeContext.ofList free) bound replacement (.base row.name))) := by
  intro remaining
  induction remaining with
  | nil => schema_eval using (agreement)
  | cons row remaining induction =>
      have checkedBody := bodyReturns (.base row.name)
      have checkedReplacement := replacementReturns (.base row.name)
      cases first : checkSchemaHasType language (FreeTypeContext.ofList free)
        (.base row.name :: bound) body expected <;> rw [first] at checkedBody
      · schema_eval using (agreement) [checkedBody,induction] unfolding [List.any_cons,first,typeTerm]
      · cases second : checkSchemaHasType language (FreeTypeContext.ofList free)
          bound replacement (.base row.name) <;> rw [second] at checkedReplacement
        · schema_eval using (agreement) [checkedBody,checkedReplacement,induction]
            unfolding [List.any_cons,first,second,typeTerm]
        · schema_eval using (agreement) [checkedBody,checkedReplacement]
            unfolding [List.any_cons,first,second,typeTerm]

#print axioms substitutions_returns_of

private theorem bareCollectionElementType_multiple (row : GrammarRule) (kind : CollType)
    (expected : TypeExpr) (first second : TermParam) (later : List TermParam)
    (shape : row.bareParams = first :: second :: later) :
    bareCollectionElementType? row kind expected = none := by
  cases result : bareCollectionElementType? row kind expected with
  | none => rfl
  | some elementType =>
      obtain ⟨_,name,parameters⟩ := (bareCollectionElementType?_eq_some_iff ..).mp result
      simp only [shape,List.cons.injEq,List.cons_ne_nil,and_false] at parameters

include agreement in
theorem collections_returns_of (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (kind : CollType) (elements : List Pattern) (rest : Option String) (expected : TypeExpr)
    (children : ∀ child ∈ elements, ∀ type,
      PureReturns program [] host
        (apply "gslt:premise:schema-has" [encoded (sortsTerm language),encoded (declarationsTerm language),
          encoded (freeTerm free),encoded (encodeList typeTerm bound),encoded (encodePattern child),encoded (typeTerm type)])
        host (Effects.boolean (checkSchemaHasType language (FreeTypeContext.ofList free) bound child type))) :
    ∀ (remaining : List GrammarRule),
    PureReturns program [] host
      (apply "gslt:premise:schema-collections" [encoded (sortsTerm language),encoded (declarationsTerm language),
        encoded (freeTerm free),encoded (encodeList typeTerm bound),
        encoded (InferenceCettaWire.encodeCollectionType kind),encoded (encodeList encodePattern elements),
        encoded (InferenceCettaWire.encodeRest rest),encoded (typeTerm expected),
        encoded (encodeList typingDeclarationTerm remaining)])
      host (Effects.boolean (remaining.any fun row =>
        match bareCollectionElementType? row kind expected with
        | some elementType => checkSchemaElements language (FreeTypeContext.ofList free) bound elements elementType &&
            checkRestHasType (FreeTypeContext.ofList free) kind elementType rest
        | none => false)) := by
  intro remaining
  induction remaining with
  | nil => schema_eval using (agreement)
  | cons row remaining induction =>
      rcases row with ⟨label,category,parameters,syntaxRows,evaluation,algebra,representation⟩
      cases representation with
      | wrapped =>
          cases expected <;>
            schema_eval using (agreement) [induction] unfolding
              [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
      | bare =>
          cases parameters with
          | nil =>
              cases expected <;>
                schema_eval using (agreement) [induction] unfolding
                  [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
          | cons parameter parameters =>
              cases parameters with
              | cons second later =>
                  have noElement := bareCollectionElementType_multiple
                    ⟨label,category,parameter :: second :: later,syntaxRows,evaluation,algebra,.bare⟩
                    kind expected parameter second later rfl
                  simp only [List.any_cons,noElement,Bool.false_or]
                  cases expected <;>
                    schema_eval using (agreement) [induction] unfolding
                      [GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
              | nil =>
                  cases parameter with
                  | abstractionNamed binder name type =>
                      cases expected <;>
                        schema_eval using (agreement) [induction] unfolding
                          [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                  | multiAbstractionNamed binders name type =>
                      cases expected <;>
                        schema_eval using (agreement) [induction] unfolding
                          [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                  | simple name parameterType =>
                      cases parameterType with
                      | base sort =>
                          cases expected <;>
                            schema_eval using (agreement) [induction] unfolding
                              [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                      | arrow domain codomain =>
                          cases expected <;>
                            schema_eval using (agreement) [induction] unfolding
                              [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                      | multiBinder domain =>
                          cases expected <;>
                            schema_eval using (agreement) [induction] unfolding
                              [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                      | collection actual elementType =>
                          cases expected with
                          | arrow domain codomain =>
                              schema_eval using (agreement) [induction] unfolding
                                [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                          | multiBinder domain =>
                              schema_eval using (agreement) [induction] unfolding
                                [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                          | collection another type =>
                              schema_eval using (agreement) [induction] unfolding
                                [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm]
                          | base sort =>
                              have elementsChecked := elements_returns_of program agreement host language free bound elementType elements children
                              have restChecked := rest_returns program agreement host free kind elementType rest
                              by_cases categorySame : category = sort <;>
                                cases actual <;> cases kind <;>
                                  cases elementsResult : checkSchemaElements language (FreeTypeContext.ofList free) bound elements elementType <;>
                                    rw [elementsResult] at elementsChecked <;>
                                    cases restResult : checkRestHasType (FreeTypeContext.ofList free) _ elementType rest <;>
                                      rw [restResult] at restChecked <;>
                                      schema_eval using (agreement) [elementsChecked,restChecked,induction] unfolding
                                        [List.any_cons,bareCollectionElementType?,GrammarRule.bareParams,typingDeclarationTerm,typeTerm,
                                         categorySame,elementsResult,restResult,and_self,ite_true,ite_false,
                                         false_and,and_false,true_and,and_true]

#print axioms collections_returns_of

#print axioms constructors_returns_of

#print axioms checked
#print axioms binding_returns
#print axioms row_returns
#print axioms parameter_returns
#print axioms representation_returns
#print axioms extend_returns
#print axioms rest_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema
