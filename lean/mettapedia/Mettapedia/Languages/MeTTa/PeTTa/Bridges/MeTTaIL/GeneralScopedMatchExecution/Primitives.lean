import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

/-!
# Primitive execution and wire for the original general scoped matcher

The encodings retain the original requests, task agendas, assignments and
physical bag-choice histories. The primitive operations use the common scoped
source quotation and preserve the original capture and residual semantics.
-/
set_option Elab.async false

section MatcherWire
/-! Data encodings of the original scoped matcher. The original assignments,
tasks, residual choice histories and emitted answer occurrences remain present. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching

private abbrev MatcherWire_assignmentTerm (assignment : Assignment) : Term :=
  RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment
private abbrev MatcherWire_naturalsTerm (indices : List Nat) : Term := encodeList Term.natural indices
private abbrev MatcherWire_patternsTerm (patterns : List Pattern) : Term := InferenceCettaWire.encodePatterns patterns

def bagChoiceTerm (choice : GeneralScopedMatchMachine.BagChoice) : Term :=
  .application "BagChoice" [MatcherWire_naturalsTerm choice.path, .natural choice.selected]

def traceTerm (choices : List GeneralScopedMatchMachine.BagChoice) : Term := encodeList bagChoiceTerm choices

def matcherAnswerTerm (answer : GeneralScopedMatchMachine.Answer) : Term :=
  .application "ScopedMatcherAnswer" [MatcherWire_assignmentTerm answer.assignment, traceTerm answer.trace]

def matcherRequestTerm (request : GeneralScopedMatchMachine.Request) : Term :=
  .application "ScopedMatcherRequest" [InferenceCettaWire.AuthoredRule.rewriteTerm request.rule,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec, .natural request.ambient,
    InferenceCettaWire.AuthoredRule.siteTerm request.site, MatcherWire_naturalsTerm request.path, .natural request.depth,
    MatcherWire_assignmentTerm request.initial, InferenceCettaWire.encodePattern request.schema,
    InferenceCettaWire.encodePattern request.target]

def matcherTaskTerm : GeneralScopedMatchMachine.Task → Term
  | .tree path depth schema target => .application "ScopedMatcherTree"
      [MatcherWire_naturalsTerm path, .natural depth, InferenceCettaWire.encodePattern schema, InferenceCettaWire.encodePattern target]
  | .arguments path depth index schemas targets => .application "ScopedMatcherArguments"
      [MatcherWire_naturalsTerm path, .natural depth, .natural index, MatcherWire_patternsTerm schemas, MatcherWire_patternsTerm targets]
  | .bag path depth index schemas rest kind targets => .application "ScopedMatcherBag"
      [MatcherWire_naturalsTerm path, .natural depth, .natural index, MatcherWire_patternsTerm schemas,
        InferenceCettaWire.encodeRest rest, InferenceCettaWire.encodeCollectionType kind, MatcherWire_patternsTerm targets]
  | .bagSelect path depth index schema schemas rest kind targets selected => .application "ScopedMatcherBagSelect"
      [MatcherWire_naturalsTerm path, .natural depth, .natural index, InferenceCettaWire.encodePattern schema,
        MatcherWire_patternsTerm schemas, InferenceCettaWire.encodeRest rest, InferenceCettaWire.encodeCollectionType kind,
        MatcherWire_patternsTerm targets, .natural selected]
  | .restCapture path depth name kind targets => .application "ScopedMatcherRestCapture"
      [MatcherWire_naturalsTerm path, .natural depth, .string name, InferenceCettaWire.encodeCollectionType kind, MatcherWire_patternsTerm targets]

def matcherWorkTerm (work : GeneralScopedMatchMachine.Work) : Term :=
  .application "ScopedMatcherWork"
    [MatcherWire_assignmentTerm work.assignment, encodeList matcherTaskTerm work.tasks, traceTerm work.trace]

def matcherStateTerm (state : GeneralScopedMatchMachine.State) : Term :=
  .application "ScopedMatcherState"
    [encodeList matcherWorkTerm state.agenda, encodeList matcherAnswerTerm state.answers]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherWire

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.matcherStateTerm


section MatcherProgram
/-! Conservative source extension implementing original scoped matcher tasks. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects

def sourceProgram : Program := RuleExecutionProgram.scopedMatcherProgram

def eraseProgram : Program := RuleExecutionProgram.matcherEraseProgram

def extensionProgram : Program := eraseProgram.append sourceProgram

def program : Program := RuleExecutionProgram.program.append extensionProgram

def retainedHeads : List String :=
  ["gslt:automata:append", "gslt:automata:length", "gslt:automata:binding", "gslt:automata:member",
    "gslt:rule:lift-bvars", "gslt:rule:lift-bvars-list", "gslt:rule:row-at",
    "gslt:rule:scope-well-scoped", "gslt:rule:scope-well-scoped-list",
    "gslt:rule:scope-index", "gslt:rule:scope-variable-spine", "gslt:rule:scope-assignment",
    "gslt:rule:scope-substitute", "gslt:rule:scope-substitute-list", "gslt:rule:scope-instantiate-value",
    "gslt:rule:scope-recover-value", "gslt:rule:scope-assign", "gslt:rule:scope-metadata-dependency-rows",
    "gslt:rule:scope-metadata-dependencies", "gslt:rule:scope-metadata-occurrence-rows",
    "gslt:rule:scope-metadata-quantified-body", "gslt:rule:scope-metadata-site-premise",
    "gslt:rule:scope-metadata-premise-pattern", "gslt:rule:scope-metadata-site-pattern",
    "gslt:rule:scope-metadata-occurrence-name", "gslt:rule:scope-metadata-occurrence-declared",
    "gslt:rule:scope-metadata-arguments"]

def baseHead (head : String) : Bool :=
  head != "eval" && (!head.startsWith "gslt:" || retainedHeads.contains head)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherProgram

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.sourceProgram


section MatcherBodyBlock00
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_0 :
    ((RuleExecutionProgram.program.equations.drop 0).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock00

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_0


section MatcherBodyBlock01
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_1 :
    ((RuleExecutionProgram.program.equations.drop 16).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock01

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_1


section MatcherBodyBlock02
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_2 :
    ((RuleExecutionProgram.program.equations.drop 32).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock02

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_2


section MatcherBodyBlock03
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_3 :
    ((RuleExecutionProgram.program.equations.drop 48).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock03

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_3


section MatcherBodyBlock04
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_4 :
    ((RuleExecutionProgram.program.equations.drop 64).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock04

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_4


section MatcherBodyBlock05
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_5 :
    ((RuleExecutionProgram.program.equations.drop 80).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock05

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_5


section MatcherBodyBlock06
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_6 :
    ((RuleExecutionProgram.program.equations.drop 96).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock06

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_6


section MatcherBodyBlock07
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_7 :
    ((RuleExecutionProgram.program.equations.drop 112).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock07

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_7


section MatcherBodyBlock08
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_8 :
    ((RuleExecutionProgram.program.equations.drop 128).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock08

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_8


section MatcherBodyBlock09
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Eval GeneralScopedMatchExecution

private theorem base_body_block_9 :
    ((RuleExecutionProgram.program.equations.drop 144).take 16).all
      (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherBodyBlock09

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_body_block_9


section MatcherAgreement
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects

private theorem MatcherAgreement_bodies_tail_160 :
    (RuleExecutionProgram.program.equations.drop 160).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  rfl



private theorem MatcherAgreement_bodies_tail_144 :
    (RuleExecutionProgram.program.equations.drop 144).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_9
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 144), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_160


private theorem MatcherAgreement_bodies_tail_128 :
    (RuleExecutionProgram.program.equations.drop 128).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_8
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 128), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_144


private theorem MatcherAgreement_bodies_tail_112 :
    (RuleExecutionProgram.program.equations.drop 112).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_7
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 112), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_128


private theorem MatcherAgreement_bodies_tail_96 :
    (RuleExecutionProgram.program.equations.drop 96).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_6
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 96), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_112


private theorem MatcherAgreement_bodies_tail_80 :
    (RuleExecutionProgram.program.equations.drop 80).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_5
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 80), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_96


private theorem MatcherAgreement_bodies_tail_64 :
    (RuleExecutionProgram.program.equations.drop 64).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_4
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 64), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_80


private theorem MatcherAgreement_bodies_tail_48 :
    (RuleExecutionProgram.program.equations.drop 48).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_3
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 48), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_64


private theorem MatcherAgreement_bodies_tail_32 :
    (RuleExecutionProgram.program.equations.drop 32).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_2
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 32), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_48


private theorem MatcherAgreement_bodies_tail_16 :
    (RuleExecutionProgram.program.equations.drop 16).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_1
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 16), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_32

private theorem MatcherAgreement_bodies_tail_0 :
    (RuleExecutionProgram.program.equations.drop 0).all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  have front := base_body_block_0
  rw [← List.take_append_drop 16 (RuleExecutionProgram.program.equations.drop 0), List.all_append, front, Bool.true_and]
  simpa only [List.drop_drop] using MatcherAgreement_bodies_tail_16


theorem base_bodies_within :
    RuleExecutionProgram.program.equations.all (fun equation => !baseHead equation.head || codeWithin baseHead equation.body) = true := by
  simpa only [List.drop_zero] using MatcherAgreement_bodies_tail_0


theorem base_program_closed : ProgramClosed baseHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp base_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked



theorem extension_equations_fresh :
    extensionProgram.equations.all (fun equation => !baseHead equation.head) = true := by
  decide +kernel



theorem extension_declarations_fresh :
    extensionProgram.declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !baseHead head
      | _ => true) = true := by
  decide +kernel



theorem base_program_agreement :
    ProgramAgreementOn baseHead RuleExecutionProgram.program program := by
  exact appended_program_agreement_of_checks _ _ _ extension_equations_fresh
    extension_declarations_fresh (fun _ _ => rfl)


theorem base_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin baseHead code = true)
    (checked : PureReturns RuleExecutionProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement base_program_closed base_program_agreement ⟨supported, rfl⟩ checked


theorem no_initializers : extensionProgram.initializers = [] := by decide +kernel
private theorem MatcherAgreement_extension_heads_unique : (extensionProgram.equations.map (·.head)).Nodup := by
  decide +kernel

private theorem MatcherAgreement_extension_heads_disjoint :
    List.Disjoint (RuleExecutionProgram.program.equations.map (·.head))
      (extensionProgram.equations.map (·.head)) := by
  have checked : (extensionProgram.equations.map (·.head)).all
      (fun head => !(RuleExecutionProgram.program.equations.map (·.head)).any (· == head)) = true := by
    decide +kernel
  apply List.disjoint_iff_ne.mpr
  intro first firstMember second secondMember same
  have absent := List.all_eq_true.mp checked second secondMember
  have present : (RuleExecutionProgram.program.equations.map (·.head)).any (· == second) = true :=
    List.any_eq_true.mpr ⟨first, firstMember, by simp [same]⟩
  simp [present] at absent

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by
  simp only [program, SpaceSemantics.Program.append, List.map_append]
  exact List.nodup_append'.mpr
    ⟨RuleExecutionProgram.equation_heads_unique, MatcherAgreement_extension_heads_unique, MatcherAgreement_extension_heads_disjoint⟩




end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
end MatcherAgreement

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.base_captured_returns


section MatcherClauses
/-! The actual retained source implements the original scoped matcher tasks.
Assignments and physical choice histories are the original machine's data. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.MachineProofs

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution

abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
abbrev v (name : String) : Atom := .var name
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev number (value : Nat) : Atom := encoded (.natural value)
abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
abbrev assignmentValue (assignment : Assignment) : Atom := encoded (ScopedCapture.scopedAssignmentTerm assignment)
abbrev requestValue (request : GeneralScopedMatchMachine.Request) : Atom := encoded (matcherRequestTerm request)
abbrev stateValue (state : GeneralScopedMatchMachine.State) : Atom := encoded (matcherStateTerm state)

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue

inductive Helper where
  | capture | capturedWork | split | start | complete | tree | expand | branches | advance | tick | run

def Helper.head (helper : Helper) : String := "gslt:rule:scope-matcher-" ++ match helper with
  | .capture => "capture" | .capturedWork => "captured-work" | .split => "split-at" | .start => "start"
  | .complete => "complete" | .tree => "expand-tree" | .expand => "expand" | .branches => "advance-branches"
  | .advance => "advance" | .tick => "tick" | .run => "run"

def Helper.names : Helper → List String
  | .capture => ["rule", "spec", "ambient", "site", "path", "depth", "assignment", "name", "target"]
  | .capturedWork => ["captured"]
  | .split => ["count", "values"]
  | .start => ["request"]
  | .complete => ["state"]
  | .tree => ["rule", "spec", "ambient", "site", "assignment", "path", "depth", "schema", "target"]
  | .expand => ["request", "assignment", "task"]
  | .branches => ["branches", "tasks", "trace"]
  | .advance => ["request", "work"]
  | .tick => ["request", "state"]
  | .run => ["request", "fuel", "state"]

def equation (helper : Helper) : SpaceSemantics.Equation :=
  (sourceProgram.equations.filter fun row => row.head == helper.head)[0]'(by cases helper <;> decide +kernel)
def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> rfl) (by cases helper <;> decide) length

theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  have checked : (List.range helper.names.length).all (fun index => argumentIsRaw program helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom) (length : values.length = helper.names.length)
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
    (arguments values : List Atom) (answer : Atom) (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    omega
  · cases helper <;> decide
  · have emptyFunction : applySubst [] = (id : Atom → Atom) :=
      funext Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil
    rw [emptyFunction, List.map_id]
    exact captured.symm
  · exact returned

theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom)
    (fresh : Subst.lookup caller name = none)
    (returned : PureReturns program caller state expression state value)
    (continuation : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer returned _ continuation
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem option_case_returns (caller : Subst) (state : State) (code : Atom)
    (value : Option Term) (name fallback : String) (yes no answer : Atom)
    (freshName : Subst.lookup caller name = none)
    (freshFallback : Subst.lookup caller fallback = none)
    (computed : PureReturns program caller state code state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm value)))
    (stopped : value = none → PureReturns program ((fallback, .symbol "None") :: caller)
      state no state answer)
    (continued : ∀ payload, value = some payload →
      PureReturns program ((name, encoded payload) :: caller) state yes state answer) :
    PureReturns program caller state (a "case" [code,
      .expression [.expression [a "Some" [v name], yes], .expression [v fallback, no]]]) state answer := by
  cases value with
  | none =>
      apply case_returns program caller ((fallback, .symbol "None") :: caller) state state state
        code (.symbol "None") no answer _ [(a "Some" [v name], yes), (v fallback, no)]
        (read_cases_encoded _) computed _ (stopped rfl)
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, freshFallback]
  | some payload =>
      apply case_returns program caller ((name, encoded payload) :: caller) state state state
        code (a "Some" [encoded payload]) yes answer _ [(a "Some" [v name], yes), (v fallback, no)]
        (read_cases_encoded _) computed _ (continued payload rfl)
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, freshName]

def dataHeads : List String :=
  ["LCons", "Some", "ScopedMatcherRequest", "ScopedMatcherTree", "ScopedMatcherArguments", "ScopedMatcherBag",
    "ScopedMatcherBagSelect", "ScopedMatcherRestCapture", "ScopedMatcherWork", "ScopedMatcherState",
    "ScopedMatcherAnswer", "ScopedMatcherSplit", "BagChoice", "PCollection"]

theorem data_heads_inert : dataHeads.all (fun head =>
    !(ioHead head || StdLib.known head || program.equations.any (·.head == head))) = true := by
  decide +kernel

theorem data_template (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have checked := List.all_eq_true.mp data_heads_inert head member
    cases result : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) with
    | false => rfl
    | true => simp [result] at checked
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

syntax "wire_template" : tactic
macro_rules
  | `(tactic| wire_template) => `(tactic|
  first
  | exact PureData.Template.captured _
  | exact PureData.Template.symbol _
  | exact PureData.Template.grounded _
  | apply data_template _ _ (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    repeat' (first | (rcases member with rfl | member) | (subst argument))
    all_goals wire_template)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.MachineProofs
end MatcherClauses


section MatcherState
/-! The actual retained source implements the original scoped matcher tasks.
Assignments and physical choice histories are the original machine's data. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs


attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue

def matcherStartTerm (request : GeneralScopedMatchMachine.Request) : Term :=
  .application "gslt:rule:scope-matcher-start" [matcherRequestTerm request]

def matcherCompleteTerm (state : GeneralScopedMatchMachine.State) : Term :=
  .application "gslt:rule:scope-matcher-complete" [matcherStateTerm state]

def matcherTickTerm (request : GeneralScopedMatchMachine.Request) (state : GeneralScopedMatchMachine.State) : Term :=
  .application "gslt:rule:scope-matcher-tick" [matcherRequestTerm request, matcherStateTerm state]

def matcherRunTerm (request : GeneralScopedMatchMachine.Request) (fuel : Nat)
    (state : GeneralScopedMatchMachine.State) : Term :=
  .application "gslt:rule:scope-matcher-run" [matcherRequestTerm request, .natural fuel, matcherStateTerm state]

private def MatcherState_startResult : Atom := a "ScopedMatcherState"
  [a "LCons" [a "ScopedMatcherWork" [v "initial", a "LCons"
    [a "ScopedMatcherTree" [v "path", v "depth", v "schema", v "target"], .symbol "LNil"], .symbol "LNil"], .symbol "LNil"],
   .symbol "LNil"]
private def MatcherState_startCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherRequest" (["rule", "spec", "ambient", "site", "path", "depth", "initial", "schema", "target"].map v),
    MatcherState_startResult)]
private theorem MatcherState_start_shape : (equation .start).body =
    a "case" [v "request", .expression (MatcherState_startCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem MatcherState_start_template : PureData.Template program MatcherState_startResult := by
  unfold MatcherState_startResult
  wire_template

theorem matcher_start_returns (state : State) (request : GeneralScopedMatchMachine.Request) :
    PureReturns program [] state (encoded (matcherStartTerm request)) state
      (stateValue (GeneralScopedMatchMachine.start request)) := by
  let caller := environment .start [requestValue request]
  let selected := ("target", patternValue request.target) :: ("schema", patternValue request.schema) ::
    ("initial", assignmentValue request.initial) :: ("depth", number request.depth) ::
    ("path", encoded (encodeList Term.natural request.path)) ::
    ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm request.site)) :: ("ambient", number request.ambient) ::
    ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec)) ::
    ("rule", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule)) :: caller
  change PureReturns program [] state (a Helper.start.head [requestValue request]) state _
  apply helper_call .start [] state _ [requestValue request] _ rfl (by simp)
  rw [MatcherState_start_shape]
  apply case_returns program caller selected state state state (v "request") (requestValue request)
    MatcherState_startResult _ _ MatcherState_startCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "request"
  · simp [MatcherState_startCases, matcherRequestTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
  · simpa [MatcherState_startResult, selected, caller, environment, Helper.names, matcherStateTerm, matcherWorkTerm,
      matcherTaskTerm, GeneralScopedMatchMachine.start, traceTerm, ScopedCapture.scopedAssignmentTerm,
      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program selected state MatcherState_startResult MatcherState_start_template


private def MatcherState_completeAgendaCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
    (a "LCons" [v "work", v "rest"], Effects.boolean false)]
private def MatcherState_completeAgendaBody : Atom :=
  a "case" [v "agenda", .expression (MatcherState_completeAgendaCases.map fun row => .expression [row.1, row.2])]
private def MatcherState_completeCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherState" [v "agenda", v "answers"], MatcherState_completeAgendaBody)]
private theorem MatcherState_complete_shape : (equation .complete).body =
    a "case" [v "state", .expression (MatcherState_completeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem matcher_complete_returns (state : State) (machine : GeneralScopedMatchMachine.State) :
    PureReturns program [] state (encoded (matcherCompleteTerm machine)) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  let caller := environment .complete [stateValue machine]
  let selected := ("answers", encoded (encodeList matcherAnswerTerm machine.answers)) ::
    ("agenda", encoded (encodeList matcherWorkTerm machine.agenda)) :: caller
  change PureReturns program [] state (a Helper.complete.head [stateValue machine]) state _
  apply helper_call .complete [] state _ [stateValue machine] _ rfl (by simp)
  rw [MatcherState_complete_shape]
  apply case_returns program caller selected state state state (v "state") (stateValue machine)
    MatcherState_completeAgendaBody _ _ MatcherState_completeCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "state"
  · simp [MatcherState_completeCases, matcherStateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
  · unfold MatcherState_completeAgendaBody
    cases agenda : machine.agenda with
    | nil =>
        apply case_returns program selected selected state state state (v "agenda") (.symbol "LNil")
          (Effects.boolean true) _ _ MatcherState_completeAgendaCases (read_cases_encoded _)
        · simpa [selected, agenda, applySubst, Subst.lookup, CettaWireAtom.encode, encodeList] using
            variable_returns program selected state "agenda"
        · simp [MatcherState_completeAgendaCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [GeneralScopedMatchMachine.complete, agenda, Effects.boolean] using
            grounded_returns program selected state (.bool true)
    | cons work rest =>
        let branch := ("rest", encoded (encodeList matcherWorkTerm rest)) ::
          ("work", encoded (matcherWorkTerm work)) :: selected
        apply case_returns program selected branch state state state (v "agenda")
          (a "LCons" [encoded (matcherWorkTerm work), encoded (encodeList matcherWorkTerm rest)])
          (Effects.boolean false) _ _ MatcherState_completeAgendaCases (read_cases_encoded _)
        · simpa [selected, agenda, applySubst, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            encodeList] using variable_returns program selected state "agenda"
        · simp [MatcherState_completeAgendaCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, branch, selected, caller,
            environment, Helper.names, Subst.lookup]
        · simpa [GeneralScopedMatchMachine.complete, agenda, Effects.boolean] using
            grounded_returns program branch state (.bool false)


theorem matcher_start_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (argument : Atom)
    (captured : applySubst caller argument = requestValue request) :
    PureReturns program caller state (a Helper.start.head [argument]) state
      (stateValue (GeneralScopedMatchMachine.start request)) := by
  apply helper_capture .start caller state _ [requestValue request] _ rfl (by simp [captured])
  exact matcher_start_returns state request

theorem matcher_complete_captured_returns (caller : Subst) (state : State)
    (machine : GeneralScopedMatchMachine.State) (argument : Atom)
    (captured : applySubst caller argument = stateValue machine) :
    PureReturns program caller state (a Helper.complete.head [argument]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  apply helper_capture .complete caller state _ [stateValue machine] _ rfl (by simp [captured])
  exact matcher_complete_returns state machine


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherState


section MatcherErase
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.CoherentErase

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number

def termListValue (values : List Term) : Atom := encoded (encodeList id values)
private def MatcherErase_eraseHead : String := "gslt:rule:scope-match-erase-at"
private def MatcherErase_eraseNames : List String := ["index", "targets"]
private def MatcherErase_eraseEquation : SpaceSemantics.Equation := eraseProgram.equations[0]'(by decide +kernel)
private def MatcherErase_eraseEnvironment (values : List Atom) : Subst := (MatcherErase_eraseNames.zip values).reverse

private theorem MatcherErase_erase_clause (values : List Atom) (length : values.length = 2) :
    clauses program MatcherErase_eraseHead values = [.evaluate (MatcherErase_eraseEnvironment values) MatcherErase_eraseEquation.body] :=
  PureData.named_equation_clause program MatcherErase_eraseHead MatcherErase_eraseEquation MatcherErase_eraseNames values
    (by rfl) (by rfl) (by decide) length

private theorem MatcherErase_erase_call (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom) (length : values.length = 2)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (MatcherErase_eraseEnvironment values) state MatcherErase_eraseEquation.body state answer) :
    PureReturns program caller state (a MatcherErase_eraseHead arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (MatcherErase_eraseEnvironment values) state state
    MatcherErase_eraseHead arguments MatcherErase_eraseEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel)
  · intro index bounded
    have same : arguments.length = 2 := by simpa [length] using congrArg List.length captured
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact MatcherErase_erase_clause values length
  · exact returned

private theorem MatcherErase_erase_capture (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom) (length : values.length = 2)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a MatcherErase_eraseHead values) state answer) :
    PureReturns program caller state (a MatcherErase_eraseHead arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state MatcherErase_eraseHead values arguments answer
    (by decide +kernel) _ (by decide) _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> decide +kernel
  · have emptyFunction : applySubst [] = (id : Atom → Atom) :=
      funext Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil
    rw [emptyFunction, List.map_id]
    exact captured.symm

private def MatcherErase_eraseNextBody : Atom := a "let"
  [v "previous", a "-" [v "index", number 1],
   a "let" [v "remaining", a MatcherErase_eraseHead [v "previous", v "tail"],
     a "LCons" [v "target", v "remaining"]]]
private def MatcherErase_eraseConsBody : Atom := a "if" [a "==" [v "index", number 0], v "tail", MatcherErase_eraseNextBody]
private def MatcherErase_eraseCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "target", v "tail"], MatcherErase_eraseConsBody)]
private theorem MatcherErase_erase_shape : (MatcherErase_eraseEquation).body =
    a "case" [v "targets", .expression (MatcherErase_eraseCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- Indexed removal consumes one physical occurrence. Equal neighbouring
values remain separate entries; an out-of-range index retains the list. -/
theorem erase_at_returns (state : State) (index : Nat) (values : List Term) :
    PureReturns program [] state (a MatcherErase_eraseHead [number index, termListValue values]) state
      (termListValue (values.eraseIdx index)) := by
  induction values generalizing index with
  | nil =>
      let caller := MatcherErase_eraseEnvironment [number index, termListValue []]
      apply MatcherErase_erase_call [] state [number index, termListValue []] [number index, termListValue []] _ rfl (by simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherErase_erase_shape]
      apply case_returns program caller caller state state state (v "targets") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ MatcherErase_eraseCases (read_cases_encoded _) _ _ _
      · simpa [caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, termListValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "targets"
      · simp [MatcherErase_eraseCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first values ih =>
      let caller := MatcherErase_eraseEnvironment [number index, termListValue (first :: values)]
      let selected := ("tail", termListValue values) :: ("target", encoded first) :: caller
      have tested := CettaWireAtom.equality_evaluated_returns program selected state (.natural index) (.natural 0)
        (v "index") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, applySubst, Subst.lookup] using
          variable_returns program selected state "index")
        (grounded_returns program selected state (.int 0))
      simp only [Term.natural.injEq] at tested
      apply MatcherErase_erase_call [] state [number index, termListValue (first :: values)] [number index, termListValue (first :: values)] _ rfl (by simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherErase_erase_shape]
      apply case_returns program caller selected state state state (v "targets")
        (termListValue (first :: values)) MatcherErase_eraseConsBody _ _ MatcherErase_eraseCases (read_cases_encoded _) _ _ _
      · simpa [caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, applySubst, Subst.lookup] using
          variable_returns program caller state "targets"
      · simp [MatcherErase_eraseCases, termListValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, Subst.lookup]
      · unfold MatcherErase_eraseConsBody
        apply bool_if_returns selected state _ _ _ _ _ tested
        cases index with
        | zero =>
            simpa [termListValue, selected, applySubst, Subst.lookup] using
              variable_returns program selected state "tail"
        | succ index =>
            simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte, List.eraseIdx_cons_succ]
            let previousBound := ("previous", number index) :: selected
            let final := ("remaining", termListValue (values.eraseIdx index)) :: previousBound
            have previous : PureReturns program selected state (a "-" [v "index", number 1]) state (number index) := by
              apply native_binary_call_returns program selected state state state state "-"
                (v "index") (number 1) (number (index + 1)) (number 1) (number index)
                (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
              · simpa [selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, applySubst, Subst.lookup] using
                  variable_returns program selected state "index"
              · exact grounded_returns program selected state (.int 1)
              · change (Except.ok (state, [Atom.grounded (.int (((index + 1 : Nat) : Int) - 1))]) :
                    Effects.Result) = Except.ok (state, [.grounded (.int (index : Int))])
                simp
            have remaining := MatcherErase_erase_capture previousBound state [v "previous", v "tail"]
              [number index, termListValue values] _ rfl
              (by simp [previousBound, selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, applySubst, Subst.lookup]) (ih index)
            apply named_let_returns selected state "previous" _ _ _ _
                (by simp [selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, Subst.lookup]) previous
            apply named_let_returns previousBound state "remaining" _ _ _ _
                (by simp [previousBound, selected, caller, MatcherErase_eraseEnvironment, MatcherErase_eraseNames, Subst.lookup]) remaining
            simpa [termListValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              final, previousBound, selected, applySubst, applySubst.applySubstList, Subst.lookup] using
              constructor_variables_return program final state "LCons" ["target", "remaining"]
                (by decide +kernel) (by decide)

theorem erase_at_captured_returns (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [number index, termListValue values]) :
    PureReturns program caller state (a MatcherErase_eraseHead [one, two]) state
      (termListValue (values.eraseIdx index)) :=
  MatcherErase_erase_capture caller state _ _ _ rfl captured (erase_at_returns state index values)



end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution.CoherentErase
end MatcherErase


section MatcherPrimitives
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue
private abbrev MatcherPrimitives_listValue (values : List Term) : Atom := encoded (encodeList id values)

private inductive MatcherPrimitives_Primitive where
  | append | length | row | erase
private def MatcherPrimitives_Primitive.head : MatcherPrimitives_Primitive → String
  | .append => "gslt:automata:append" | .length => "gslt:automata:length"
  | .row => "gslt:rule:row-at" | .erase => "gslt:rule:scope-match-erase-at"
private def MatcherPrimitives_Primitive.arity : MatcherPrimitives_Primitive → Nat
  | .length => 1 | _ => 2

private theorem MatcherPrimitives_primitive_capture (primitive : MatcherPrimitives_Primitive) (first second : Subst) (state : State)
    (one two : List Atom) (answer : Atom) (length : one.length = primitive.arity)
    (captured : one.map (applySubst first) = two.map (applySubst second))
    (returned : PureReturns program first state (a primitive.head one) state answer) :
    PureReturns program second state (a primitive.head two) state answer := by
  apply PureData.raw_capture_returns program first second state state primitive.head one two answer
  · cases primitive <;> decide +kernel
  · intro index bounded
    have checked : (List.range primitive.arity).all
        (fun index => argumentIsRaw program primitive.head index) = true := by
      cases primitive <;> decide +kernel
    exact List.all_eq_true.mp checked index (List.mem_range.mpr (by omega))
  · cases primitive <;> decide
  · exact captured
  · exact returned

theorem matcher_append_captured_returns (caller : Subst) (state : State) (left right : List Term)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [MatcherPrimitives_listValue left, MatcherPrimitives_listValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (MatcherPrimitives_listValue (left ++ right)) := by
  let first : Subst := [("right", MatcherPrimitives_listValue right), ("left", MatcherPrimitives_listValue left)]
  have returned := base_captured_returns (by decide +kernel)
    (RuleExecutionProgram.automata_captured_returns (by decide +kernel)
      (MatchAutomataSourceExecution.append_captured_returns first state left right (v "left") (v "right")
        (by simp [first, MatcherPrimitives_listValue, MatchAutomataSourceExecution.listValue, applySubst, Subst.lookup])))
  apply MatcherPrimitives_primitive_capture .append first caller state [v "left", v "right"] [one, two] _ rfl _ returned
  simpa [first, applySubst, Subst.lookup] using captured.symm

theorem matcher_length_captured_returns (caller : Subst) (state : State) (values : List Term)
    (argument : Atom) (captured : applySubst caller argument = MatcherPrimitives_listValue values) :
    PureReturns program caller state (a "gslt:automata:length" [argument]) state (number values.length) := by
  let first : Subst := [("values", MatcherPrimitives_listValue values)]
  have returned := base_captured_returns (by decide +kernel)
    (RuleExecutionProgram.automata_captured_returns (by decide +kernel)
      (MatchAutomataSourceExecution.length_captured_returns first state values (v "values")
        (by simp [first, MatcherPrimitives_listValue, MatchAutomataSourceExecution.listValue, applySubst, Subst.lookup])))
  apply MatcherPrimitives_primitive_capture .length first caller state [v "values"] [argument] _ rfl _ returned
  simp [first, applySubst, Subst.lookup, captured]

theorem matcher_row_captured_returns (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [number index, MatcherPrimitives_listValue values]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm values[index]?)) := by
  let first : Subst := [("values", MatcherPrimitives_listValue values), ("index", number index)]
  have returned := base_captured_returns (by decide +kernel)
    (RowLookup.row_at_captured_returns first state index values (v "index") (v "values")
      (by simp [first, MatcherPrimitives_listValue, applySubst, Subst.lookup]))
  apply MatcherPrimitives_primitive_capture .row first caller state [v "index", v "values"] [one, two] _ rfl _ returned
  simpa [first, applySubst, Subst.lookup] using captured.symm

theorem matcher_erase_captured_returns (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [number index, MatcherPrimitives_listValue values]) :
    PureReturns program caller state (a "gslt:rule:scope-match-erase-at" [one, two]) state
      (MatcherPrimitives_listValue (values.eraseIdx index)) := by
  let first : Subst := [("values", MatcherPrimitives_listValue values), ("index", number index)]
  have returned := CoherentErase.erase_at_captured_returns first state index values (v "index") (v "values")
    (by simp [first, MatcherPrimitives_listValue, CoherentErase.termListValue, applySubst, Subst.lookup])
  apply MatcherPrimitives_primitive_capture .erase first caller state [v "index", v "values"] [one, two] _ rfl _ returned
  simpa [first, applySubst, Subst.lookup] using captured.symm

theorem matcher_add_returns (caller : Subst) (state : State) (left right : Nat) (one two : Atom)
    (first : PureReturns program caller state one state (number left))
    (second : PureReturns program caller state two state (number right)) :
    PureReturns program caller state (a "+" [one, two]) state (number (left + right)) := by
  apply native_binary_call_returns program caller state state state state "+"
    one two (number left) (number right) (number (left + right))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) first second _ (by decide)
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherPrimitives


section MatcherCapture
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue

def matcherCaptureTerm (request : GeneralScopedMatchMachine.Request) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) (target : Pattern) : Term :=
  .application "gslt:rule:scope-matcher-capture"
    [InferenceCettaWire.AuthoredRule.rewriteTerm request.rule,
      InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec, .natural request.ambient,
      InferenceCettaWire.AuthoredRule.siteTerm request.site, encodeList Term.natural path, .natural depth,
      ScopedCapture.scopedAssignmentTerm assignment, .string name, InferenceCettaWire.encodePattern target]

private def MatcherCapture_captureAssignBody : Atom :=
  a "gslt:rule:scope-assign" [v "assignment", v "name", v "value"]
private def MatcherCapture_captureRecoverBody : Atom :=
  a "case" [a "gslt:rule:scope-recover-value" [v "dependencies", v "ambient", v "depth", v "arguments", v "target"],
    .expression [.expression [a "Some" [v "value"], MatcherCapture_captureAssignBody], .expression [v "failed", .symbol "None"]]]
private def MatcherCapture_captureArgumentsBody : Atom :=
  a "case" [a "gslt:rule:scope-metadata-arguments" [v "rule", v "spec", v "name", v "site", v "path"],
    .expression [.expression [a "Some" [v "arguments"], MatcherCapture_captureRecoverBody], .expression [v "no-arguments", .symbol "None"]]]
private def MatcherCapture_captureDependenciesBody : Atom :=
  a "case" [a "gslt:rule:scope-metadata-dependencies" [v "spec", v "name"],
    .expression [.expression [a "Some" [v "dependencies"], MatcherCapture_captureArgumentsBody], .expression [v "no-dependencies", .symbol "None"]]]
private theorem MatcherCapture_capture_shape : (equation .capture).body = MatcherCapture_captureDependenciesBody := by decide +kernel

theorem matcher_capture_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (name : String) (target : Pattern) :
    PureReturns program [] state (encoded (matcherCaptureTerm request path depth assignment name target)) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (ScopedRuleMatching.capture? request.rule request.spec request.ambient depth request.site path assignment name target))) := by
  let values := [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
    encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec), number request.ambient,
    encoded (InferenceCettaWire.AuthoredRule.siteTerm request.site), encoded (encodeList Term.natural path),
    number depth, assignmentValue assignment, encoded (.string name), patternValue target]
  let caller := environment .capture values
  change PureReturns program [] state (a Helper.capture.head values) state _
  apply helper_call .capture [] state _ values _ rfl (by simp [values])
  rw [MatcherCapture_capture_shape]
  unfold MatcherCapture_captureDependenciesBody
  apply option_case_returns caller state _
    ((RuleBinding.dependencies? request.spec name).map (encodeList InferenceCettaWire.AuthoredRule.typeTerm))
    "dependencies" "no-dependencies" _ _ _
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · have returned := base_captured_returns (by decide +kernel)
      (ScopedMetadata.dependencies_captured_returns caller state request.spec name (v "spec") (v "name")
        (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]))
    cases found : RuleBinding.dependencies? request.spec name <;>
      simpa only [found, ScopedMetadata.dependencyOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
  · intro stopped
    have missing : RuleBinding.dependencies? request.spec name = none := by
      cases found : RuleBinding.dependencies? request.spec name with
      | none => rfl
      | some dependencies => simp [found] at stopped
    simpa [ScopedRuleMatching.capture?, missing, ScopedCapture.scopedAssignmentOptionTerm,
      MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using
      symbol_returns program _ state "None"
  · intro payload present
    cases depsFound : RuleBinding.dependencies? request.spec name with
    | none => simp [depsFound] at present
    | some dependencies =>
        have same : payload = encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies := by
          simpa [depsFound] using present.symm
        subst payload
        let depsCaller := ("dependencies", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies)) :: caller
        unfold MatcherCapture_captureArgumentsBody
        apply option_case_returns depsCaller state _
          ((RuleBinding.arguments? request.rule request.spec name request.site path).map InferenceCettaWire.encodePatterns)
          "arguments" "no-arguments" _ _ _
        · simp [depsCaller, caller, values, environment, Helper.names, Subst.lookup]
        · simp [depsCaller, caller, values, environment, Helper.names, Subst.lookup]
        · exact base_captured_returns (by decide +kernel)
            (ScopedMetadata.arguments_captured_returns depsCaller state request.rule request.spec name request.site path
              (v "rule") (v "spec") (v "name") (v "site") (v "path")
              (by simp [depsCaller, caller, values, environment, Helper.names, applySubst, Subst.lookup]))
        · intro stopped
          have missing : RuleBinding.arguments? request.rule request.spec name request.site path = none := by
            cases found : RuleBinding.arguments? request.rule request.spec name request.site path with
            | none => rfl
            | some arguments => simp [found] at stopped
          simpa [ScopedRuleMatching.capture?, depsFound, missing, ScopedCapture.scopedAssignmentOptionTerm,
            MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using
            symbol_returns program _ state "None"
        · intro payload present
          cases argsFound : RuleBinding.arguments? request.rule request.spec name request.site path with
          | none => simp [argsFound] at present
          | some arguments =>
              have same : payload = InferenceCettaWire.encodePatterns arguments := by
                simpa [argsFound] using present.symm
              subst payload
              let argsCaller := ("arguments", patternsValue arguments) :: depsCaller
              unfold MatcherCapture_captureRecoverBody
              apply option_case_returns argsCaller state _
                ((RuleBinding.recoverValue? dependencies request.ambient depth arguments target).map
                  InferenceCettaWire.AuthoredRule.contextualValueTerm)
                "value" "failed" _ _ _
              · simp [argsCaller, depsCaller, caller, values, environment, Helper.names, Subst.lookup]
              · simp [argsCaller, depsCaller, caller, values, environment, Helper.names, Subst.lookup]
              · have returned := base_captured_returns (by decide +kernel)
                  (ScopedCapture.recover_value_captured_returns argsCaller state dependencies request.ambient depth arguments target
                    (v "dependencies") (v "ambient") (v "depth") (v "arguments") (v "target")
                    (by simp [argsCaller, depsCaller, caller, values, environment, Helper.names,
                      applySubst, Subst.lookup, InferenceCettaWire.encodeList]))
                simpa only [ScopedCapture.contextualValueOptionTerm] using returned
              · intro stopped
                have missing : RuleBinding.recoverValue? dependencies request.ambient depth arguments target = none := by
                  cases found : RuleBinding.recoverValue? dependencies request.ambient depth arguments target with
                  | none => rfl
                  | some value => simp [found] at stopped
                simpa [ScopedRuleMatching.capture?, depsFound, argsFound, missing,
                  ScopedCapture.scopedAssignmentOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
                  CettaWireAtom.encode] using symbol_returns program _ state "None"
              · intro payload present
                cases recovered : RuleBinding.recoverValue? dependencies request.ambient depth arguments target with
                | none => simp [recovered] at present
                | some value =>
                    have same : payload = InferenceCettaWire.AuthoredRule.contextualValueTerm value := by
                      simpa [recovered] using present.symm
                    subst payload
                    let valueCaller := ("value", encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value)) :: argsCaller
                    have returned := base_captured_returns (by decide +kernel)
                      (ScopedCapture.assign_captured_returns valueCaller state assignment name value
                        (v "assignment") (v "name") (v "value")
                        (by simp [valueCaller, argsCaller, depsCaller, caller, values, environment,
                          Helper.names, applySubst, Subst.lookup]))
                    simpa [ScopedRuleMatching.capture?, depsFound, argsFound, recovered,
                      MatcherCapture_captureAssignBody, valueCaller] using returned

theorem matcher_capture_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) (target : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec), number request.ambient,
        encoded (InferenceCettaWire.AuthoredRule.siteTerm request.site), encoded (encodeList Term.natural path),
        number depth, assignmentValue assignment, encoded (.string name), patternValue target]) :
    PureReturns program caller state (a Helper.capture.head arguments) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (ScopedRuleMatching.capture? request.rule request.spec request.ambient depth request.site path assignment name target))) := by
  apply helper_capture .capture caller state _ _ _ rfl captured
  exact matcher_capture_returns state request path depth assignment name target


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherCapture


section MatcherLists
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue

private abbrev MatcherLists_listValue (values : List Term) : Atom := encoded (encodeList id values)
private abbrev MatcherLists_splitValue (count : Nat) (values : List Term) : Atom :=
  a "ScopedMatcherSplit" [MatcherLists_listValue (values.take count), MatcherLists_listValue (values.drop count)]
private def MatcherLists_splitResult : Atom := a "ScopedMatcherSplit" [a "LCons" [v "head", v "front"], v "back"]
private def MatcherLists_splitCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "ScopedMatcherSplit" [.symbol "LNil", .symbol "LNil"]),
    (a "LCons" [v "head", v "tail"],
      a "let" [v "previous", a "-" [v "count", number 1],
        a "case" [a Helper.split.head [v "previous", v "tail"],
          .expression [.expression [a "ScopedMatcherSplit" [v "front", v "back"], MatcherLists_splitResult]]]])]
private def MatcherLists_splitPositiveBody : Atom :=
  a "case" [v "values", .expression (MatcherLists_splitCases.map fun row => .expression [row.1, row.2])]
private theorem MatcherLists_split_shape : (equation .split).body =
    a "if" [a "==" [v "count", number 0],
      a "ScopedMatcherSplit" [.symbol "LNil", v "values"], MatcherLists_splitPositiveBody] := by decide +kernel
private theorem MatcherLists_split_zero_template :
    PureData.Template program (a "ScopedMatcherSplit" [.symbol "LNil", v "values"]) := by wire_template
private theorem MatcherLists_split_result_template : PureData.Template program MatcherLists_splitResult := by
  unfold MatcherLists_splitResult
  wire_template

theorem matcher_split_returns (state : State) (count : Nat) (values : List Term) :
    PureReturns program [] state (a Helper.split.head [number count, MatcherLists_listValue values]) state
      (MatcherLists_splitValue count values) := by
  induction count generalizing values with
  | zero =>
      let caller := environment .split [number 0, MatcherLists_listValue values]
      apply helper_call .split [] state _ [number 0, MatcherLists_listValue values] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherLists_split_shape]
      apply bool_if_returns caller state _ true _ _ _
      · have returned := CettaWireAtom.equality_evaluated_returns program caller state
          (.natural 0) (.natural 0) (v "count") (number 0) (by decide +kernel) (by decide +kernel)
          (by simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns program caller state "count")
          (grounded_returns program caller state (.int 0))
        simpa only [Term.natural.injEq, decide_true] using returned
      · simpa [MatcherLists_splitValue, MatcherLists_listValue, caller, environment, Helper.names,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program caller state _ MatcherLists_split_zero_template
  | succ count ih =>
      let caller := environment .split [number (count + 1), MatcherLists_listValue values]
      apply helper_call .split [] state _ [number (count + 1), MatcherLists_listValue values] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [MatcherLists_split_shape]
      apply bool_if_returns caller state _ false _ _ _
      · have returned := CettaWireAtom.equality_evaluated_returns program caller state
          (.natural (count + 1)) (.natural 0) (v "count") (number 0) (by decide +kernel) (by decide +kernel)
          (by simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns program caller state "count")
          (grounded_returns program caller state (.int 0))
        simpa only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false] using returned
      · unfold MatcherLists_splitPositiveBody
        cases values with
        | nil =>
            apply case_returns program caller caller state state state (v "values") (.symbol "LNil")
              (a "ScopedMatcherSplit" [.symbol "LNil", .symbol "LNil"]) _ _ MatcherLists_splitCases
              (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, MatcherLists_listValue, CettaWireAtom.encode, applySubst, Subst.lookup]
                using variable_returns program caller state "values"
            · simp [MatcherLists_splitCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [MatcherLists_splitValue, MatcherLists_listValue, CettaWireAtom.encode, encodeList, applySubst, applySubst.applySubstList] using
                PureData.template_return program caller state (a "ScopedMatcherSplit" [.symbol "LNil", .symbol "LNil"])
                  (by wire_template)
        | cons head tail =>
            let selected := ("tail", MatcherLists_listValue tail) :: ("head", encoded head) :: caller
            let previous := ("previous", number count) :: selected
            let result := ("back", MatcherLists_listValue (tail.drop count)) :: ("front", MatcherLists_listValue (tail.take count)) :: previous
            apply case_returns program caller selected state state state (v "values") (MatcherLists_listValue (head :: tail))
              (a "let" [v "previous", a "-" [v "count", number 1],
                a "case" [a Helper.split.head [v "previous", v "tail"],
                  .expression [.expression [a "ScopedMatcherSplit" [v "front", v "back"], MatcherLists_splitResult]]]])
              _ _ MatcherLists_splitCases (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
                variable_returns program caller state "values"
            · simp [MatcherLists_splitCases, MatcherLists_listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
            · apply named_let_returns selected state "previous" _ (number count)
              · simp [selected, caller, environment, Helper.names, Subst.lookup]
              · apply native_binary_call_returns program selected state state state state "-"
                  (v "count") (number 1) (number (count + 1)) (number 1) (number count)
                  (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
                · simpa [selected, caller, environment, Helper.names, applySubst, Subst.lookup] using
                    variable_returns program selected state "count"
                · exact grounded_returns program selected state (.int 1)
                · change (Except.ok (state, [Atom.grounded (.int (((count + 1 : Nat) : Int) - 1))]) :
                    Effects.Result) = Except.ok (state, [.grounded (.int (count : Int))])
                  simp
              · apply case_returns program previous result state state state
                  (a Helper.split.head [v "previous", v "tail"]) (MatcherLists_splitValue count tail)
                  MatcherLists_splitResult _ _ [(a "ScopedMatcherSplit" [v "front", v "back"], MatcherLists_splitResult)]
                  (read_cases_encoded _)
                · apply helper_capture .split previous state _ [number count, MatcherLists_listValue tail] _ rfl
                    (by simp [previous, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                  exact ih tail
                · simp [MatcherLists_splitValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, result, previous, selected,
                    caller, environment, Helper.names, Subst.lookup]
                · simpa [MatcherLists_splitValue, MatcherLists_splitResult, MatcherLists_listValue, result, previous, selected, caller, environment,
                    Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList] using
                    PureData.template_return program result state MatcherLists_splitResult MatcherLists_split_result_template

theorem matcher_split_captured_returns (caller : Subst) (state : State) (count : Nat)
    (values : List Term) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number count, MatcherLists_listValue values]) :
    PureReturns program caller state (a Helper.split.head [one, two]) state (MatcherLists_splitValue count values) :=
  helper_capture .split caller state _ _ _ rfl captured (matcher_split_returns state count values)

private def MatcherLists_capturedWorkCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"),
    (a "Some" [v "assignment"], a "LCons"
      [a "ScopedMatcherWork" [v "assignment", .symbol "LNil", .symbol "LNil"], .symbol "LNil"])]
private theorem MatcherLists_captured_work_shape : (equation .capturedWork).body =
    a "case" [v "captured", .expression (MatcherLists_capturedWorkCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem matcher_captured_work_returns (state : State) (captured : Option Assignment) :
    PureReturns program [] state (a Helper.capturedWork.head
      [encoded (ScopedCapture.scopedAssignmentOptionTerm captured)]) state
      (encoded (encodeList matcherWorkTerm
        (captured.toList.map fun assignment => { assignment, tasks := [], trace := [] }))) := by
  let caller := environment .capturedWork [encoded (ScopedCapture.scopedAssignmentOptionTerm captured)]
  apply helper_call .capturedWork [] state _ [encoded (ScopedCapture.scopedAssignmentOptionTerm captured)] _ rfl
    (by simp)
  rw [MatcherLists_captured_work_shape]
  cases captured with
  | none =>
      apply case_returns program caller caller state state state (v "captured") (.symbol "None")
        (.symbol "LNil") _ _ MatcherLists_capturedWorkCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup,
          ScopedCapture.scopedAssignmentOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
          CettaWireAtom.encode] using variable_returns program caller state "captured"
      · simp [MatcherLists_capturedWorkCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | some assignment =>
      let selected := ("assignment", assignmentValue assignment) :: caller
      apply case_returns program caller selected state state state (v "captured")
        (a "Some" [assignmentValue assignment]) (MatcherLists_capturedWorkCases[1]'(by decide)).2 _ _
        MatcherLists_capturedWorkCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup,
          ScopedCapture.scopedAssignmentOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using variable_returns program caller state "captured"
      · simp [MatcherLists_capturedWorkCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · simpa [MatcherLists_capturedWorkCases, selected, caller, environment, Helper.names, matcherWorkTerm, traceTerm,
          applySubst, applySubst.applySubstList, Subst.lookup, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program selected state (MatcherLists_capturedWorkCases[1]'(by decide)).2 (by wire_template)

theorem matcher_captured_work_captured_returns (caller : Subst) (state : State)
    (captured : Option Assignment) (argument : Atom)
    (same : applySubst caller argument = encoded (ScopedCapture.scopedAssignmentOptionTerm captured)) :
    PureReturns program caller state (a Helper.capturedWork.head [argument]) state
      (encoded (encodeList matcherWorkTerm
        (captured.toList.map fun assignment => { assignment, tasks := [], trace := [] }))) :=
  helper_capture .capturedWork caller state _ _ _ rfl (by simp [same])
    (matcher_captured_work_returns state captured)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherLists
