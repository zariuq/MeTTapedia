import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineTickExecution
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRenderPrograms
import Mettapedia.Languages.CHR.MachineAdvance
import Mettapedia.Languages.CHR.MachineTick

/-! The package port of a prepared CHR program over the machine: three
declarations and three equations under `lang:compiled`, whose bodies call
the machine with the program's occurrence table and seeds. Loaded after the
machine, `begin` starts the run, each `advance` runs one bounded unit, and
`outcome` reports the machine's result. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment Head Goal Rule)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table TableHeaded Ready)

/-! ## Machine data -/

/-- Atoms built from machine constructors, symbols the source reader keeps,
integers and strings. -/
inductive MachineData : Atom → Prop
  | symbol (name : String) (safe : ReadAfterRender.symbolSafe name = true) : MachineData (.symbol name)
  | integer (value : Int) : MachineData (.grounded (.int value))
  | string (value : String) : MachineData (.grounded (.string value))
  | constructor (head : String) (arguments : List Atom) (member : head ∈ machineConstructors)
      (data : ∀ argument ∈ arguments, MachineData argument) : MachineData (.expression (.symbol head :: arguments))

theorem argumentsCheck_all (program : SpaceSemantics.Program) :
    ∀ (arguments : List Atom), BridgeKit.argumentsCheck program arguments =
      arguments.all (BridgeKit.templateCheck program)
  | [] => rfl
  | first :: rest => by simp [BridgeKit.argumentsCheck, argumentsCheck_all program rest]

theorem applySubstList_closed (caller : Subst) :
    ∀ (arguments : List Atom), (∀ argument ∈ arguments, applySubst caller argument = argument) →
      applySubst.applySubstList caller arguments = arguments
  | [], _ => rfl
  | first :: rest, closed => by
    simp only [applySubst.applySubstList, closed first List.mem_cons_self,
      applySubstList_closed caller rest (fun argument member => closed argument (List.mem_cons_of_mem _ member))]

theorem machineData_template : ∀ {atom : Atom}, MachineData atom →
    BridgeKit.templateCheck runtime atom = true ∧ ∀ caller : Subst, applySubst caller atom = atom
  | _, .symbol name _ => ⟨rfl, fun _ => rfl⟩
  | _, .integer value => ⟨rfl, fun _ => rfl⟩
  | _, .string value => ⟨rfl, fun _ => rfl⟩
  | _, .constructor head arguments member data => by
    have children := fun argument (inside : argument ∈ arguments) => machineData_template (data argument inside)
    refine ⟨?_, fun caller => ?_⟩
    · simp only [BridgeKit.templateCheck, BridgeKit.itemsCheck, inert_of_mem member, Bool.true_and,
        argumentsCheck_all, List.all_eq_true]
      exact fun argument inside => (children argument inside).1
    · simp only [applySubst, applySubst.applySubstList]
      rw [applySubstList_closed caller arguments (fun argument inside => (children argument inside).2 caller)]

/-- Machine data returns itself. -/
theorem machineData_returns (caller : Subst) (state : State) {atom : Atom} (data : MachineData atom) :
    Returns caller state atom atom :=
  data_returns runtime caller state atom atom (machineData_template data).1 ((machineData_template data).2 caller)

theorem listAtom_data : ∀ (items : List Atom), (∀ item ∈ items, MachineData item) → MachineData (listAtom items)
  | [], _ => .symbol _ (by decide)
  | first :: rest, data => .constructor "ChrCons" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact data _ List.mem_cons_self
      · exact listAtom_data rest (fun item member => data item (List.mem_cons_of_mem _ member)))

theorem map_data {α : Type} (encode : α → Atom) (each : ∀ item, MachineData (encode item)) (items : List α) :
    MachineData (listAtom (items.map encode)) :=
  listAtom_data _ (fun item inside => by
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp inside
    exact each source)

theorem constructor_data (head : String) (arguments : List Atom) (member : head ∈ machineConstructors)
    (data : ∀ argument ∈ arguments, MachineData argument) : MachineData (.expression (.symbol head :: arguments)) :=
  .constructor head arguments member data

mutual
  theorem valueAtom_data : ∀ (value : Value), MachineData (valueAtom value)
    | .integer number => .integer number
    | .atom name => .string name
    | .tuple fields => .constructor "ChrTuple" _ (by decide) (by
        intro argument inside
        simp only [List.mem_singleton] at inside
        subst inside
        exact valuesAtom_data fields)
  theorem valuesAtom_data : ∀ (values : List Value), MachineData (valuesAtom values)
    | [] => .symbol _ (by decide)
    | first :: rest => .constructor "ChrCons" _ (by decide) (by
        intro argument inside
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact valueAtom_data first
        · exact valuesAtom_data rest)
end

mutual
  theorem termAtom_data : ∀ (term : Term), MachineData (termAtom term)
    | .value datum => .constructor "ChrValue" _ (by decide) (by
        intro argument inside
        simp only [List.mem_singleton] at inside
        subst inside
        exact valueAtom_data datum)
    | .var index => .constructor "ChrVar" _ (by decide) (by
        intro argument inside
        simp only [List.mem_singleton] at inside
        subst inside
        exact .integer _)
    | .tuple fields => .constructor "ChrTupleTerm" _ (by decide) (by
        intro argument inside
        simp only [List.mem_singleton] at inside
        subst inside
        exact termsAtom_data fields)
  theorem termsAtom_data : ∀ (terms : List Term), MachineData (termsAtom terms)
    | [] => .symbol _ (by decide)
    | first :: rest => .constructor "ChrCons" _ (by decide) (by
        intro argument inside
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact termAtom_data first
        · exact termsAtom_data rest)
end

theorem headAtom_data (head : Head) : MachineData (headAtom head) :=
  .constructor "ChrHead" _ (by decide) (by
    intro argument inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl
    · exact .string _
    · exact .integer _
    · exact termsAtom_data _)

theorem expressionAtom_data : ∀ (expression : Mettapedia.Languages.CHR.IntExpr),
    MachineData (expressionAtom expression)
  | .literal value => .constructor "ChrLiteral" _ (by decide) (by
      intro argument inside
      simp only [List.mem_singleton] at inside
      subst inside
      exact .integer _)
  | .index index => .constructor "ChrIndex" _ (by decide) (by
      intro argument inside
      simp only [List.mem_singleton] at inside
      subst inside
      exact .integer _)
  | .operation operator left right => .constructor "ChrOperation" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · cases operator <;> exact .symbol _ (by decide)
      · exact expressionAtom_data left
      · exact expressionAtom_data right)

theorem guardAtom_data : ∀ (guard : Mettapedia.Languages.CHR.Guard), MachineData (guardAtom guard)
  | .identical left right => .constructor "ChrIdentical" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact termAtom_data left
      · exact termAtom_data right)
  | .distinct left right => .constructor "ChrDistinct" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact termAtom_data left
      · exact termAtom_data right)
  | .compare operator left right => .constructor "ChrCompare" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · cases operator <;> exact .symbol _ (by decide)
      · exact expressionAtom_data left
      · exact expressionAtom_data right)

theorem goalAtom_data : ∀ (goal : Goal), MachineData (goalAtom goal)
  | .tell head => .constructor "ChrTell" _ (by decide) (by
      intro argument inside
      simp only [List.mem_singleton] at inside
      subst inside
      exact headAtom_data head)
  | .assign index expression => .constructor "ChrAssign" _ (by decide) (by
      intro argument inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact .integer _
      · exact expressionAtom_data expression)
  | .fail => .symbol _ (by decide)

theorem ruleAtom_data (rule : Rule) : MachineData (ruleAtom rule) :=
  .constructor "ChrRule" _ (by decide) (by
    intro argument inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl
    · exact map_data headAtom headAtom_data _
    · exact map_data headAtom headAtom_data _
    · exact map_data guardAtom guardAtom_data _
    · exact map_data goalAtom goalAtom_data _
    · unfold kindAtom
      split <;> exact .symbol _ (by decide))

theorem atAtom_data (occurrence : At) : MachineData (atAtom occurrence) :=
  .constructor "ChrAt" _ (by decide) (by
    intro argument inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl
    · exact .integer _
    · exact .integer _
    · exact ruleAtom_data _)

theorem keyAtom_data (key : Key) : MachineData (keyAtom key) :=
  .constructor "ChrKey" _ (by decide) (by
    intro argument inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact .string _
    · exact .integer _)

theorem tableAtom_data (table : Table) : MachineData (tableAtom table) :=
  map_data _ (fun entry => .constructor "ChrOccurrencesOf" _ (by decide) (by
    intro argument inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact keyAtom_data _
    · exact map_data atAtom atAtom_data _)) table

theorem programAtom_data (table : Table) : MachineData (programAtom table) :=
  .constructor "ChrProgram" _ (by decide) (by
    intro argument inside
    simp only [List.mem_singleton] at inside
    subst inside
    exact tableAtom_data table)

/-! ## The port program -/

def portBegin (table : Table) (seeds : List Head) : SpaceSemantics.Equation :=
  ⟨"lang:compiled:begin", [], apply "gslt:chr-machine:begin" [programAtom table, listAtom (seeds.map headAtom)]⟩

def portAdvance (ticks : Nat) : SpaceSemantics.Equation :=
  ⟨"lang:compiled:advance", [.var "run"], apply "gslt:chr-machine:unit" [.var "run", integer ticks]⟩

def portOutcome : SpaceSemantics.Equation :=
  ⟨"lang:compiled:outcome", [.var "run"], apply "gslt:chr-machine:outcome" [.var "run"]⟩

def arrowDeclaration (head : String) (types : List Atom) : Atom :=
  .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: types)]

/-- Begin, one bounded unit of `ticks` machine ticks, and outcome. -/
def portProgram (table : Table) (seeds : List Head) (ticks : Nat) : SpaceSemantics.Program where
  equations := [portBegin table seeds, portAdvance ticks, portOutcome]
  declarations := [arrowDeclaration "lang:compiled:begin" [.symbol "%Undefined%"],
    arrowDeclaration "lang:compiled:advance" [.symbol "Atom", .symbol "%Undefined%"],
    arrowDeclaration "lang:compiled:outcome" [.symbol "Atom", .symbol "%Undefined%"]]
  layout := [.declaration, .equation, .declaration, .equation, .declaration, .equation]

/-- The port under any entry prefix; the lang library uses `lang:compiled`. -/
def portProgramFor (entry : String) (table : Table) (seeds : List Head) (ticks : Nat) : SpaceSemantics.Program where
  equations := [⟨entry ++ ":begin", [], apply "gslt:chr-machine:begin" [programAtom table, listAtom (seeds.map headAtom)]⟩,
    ⟨entry ++ ":advance", [.var "run"], apply "gslt:chr-machine:unit" [.var "run", integer ticks]⟩,
    ⟨entry ++ ":outcome", [.var "run"], apply "gslt:chr-machine:outcome" [.var "run"]⟩]
  declarations := [arrowDeclaration (entry ++ ":begin") [.symbol "%Undefined%"],
    arrowDeclaration (entry ++ ":advance") [.symbol "Atom", .symbol "%Undefined%"],
    arrowDeclaration (entry ++ ":outcome") [.symbol "Atom", .symbol "%Undefined%"]]
  layout := [.declaration, .equation, .declaration, .equation, .declaration, .equation]

theorem portProgramFor_compiled (table : Table) (seeds : List Head) (ticks : Nat) :
    portProgramFor "lang:compiled" table seeds ticks = portProgram table seeds ticks := rfl

/-- The machine with a prepared program's port loaded after it. -/
def portRuntime (table : Table) (seeds : List Head) (ticks : Nat) : SpaceSemantics.Program :=
  runtime.append (portProgram table seeds ticks)

def portInherited (head : String) : Bool := !head.startsWith "lang:compiled:"

/-- No machine or base equation is a port head, and none calls one; decided once. -/
theorem runtime_port_free : (runtime.equations.all fun equation => portInherited equation.head &&
    codeWithin portInherited equation.body) = true := by decide +kernel

/-- No machine or base declaration declares a port head; decided once. -/
theorem runtime_port_undeclared : (runtime.declarations.all fun declaration =>
    (BridgeKit.arrowHead declaration).all portInherited) = true := by decide +kernel

theorem runtime_closed : ProgramClosed portInherited runtime := by
  refine ⟨by decide, fun equation member _ => ?_⟩
  have row := List.all_eq_true.mp runtime_port_free equation member
  simp only [Bool.and_eq_true] at row
  exact row.2

theorem port_agreement (table : Table) (seeds : List Head) (ticks : Nat) :
    ProgramAgreementOn portInherited runtime (portRuntime table seeds ticks) := by
  apply appended_program_agreement
  · intro equation member
    simp only [portProgram, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · show portInherited "lang:compiled:begin" = false
      decide +kernel
    · show portInherited "lang:compiled:advance" = false
      decide +kernel
    · show portInherited "lang:compiled:outcome" = false
      decide +kernel
  · intro name types member
    simp only [portProgram, arrowDeclaration, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same <;>
      (simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq, true_and] at same
       obtain ⟨rfl, -⟩ := same
       decide +kernel)

theorem lift_port (table : Table) (seeds : List Head) (ticks : Nat) {caller : Subst} {before after : State}
    {code answer : Atom} (within : codeWithin portInherited code = true)
    (returned : PureReturns runtime caller before code after answer) :
    PureReturns (portRuntime table seeds ticks) caller before code after answer :=
  path_of_closed_agreement runtime_closed (port_agreement table seeds ticks) ⟨within, rfl⟩ returned

theorem machineData_within : ∀ {atom : Atom}, MachineData atom → codeWithin portInherited atom = true
  | _, .symbol _ _ => rfl
  | _, .integer _ => rfl
  | _, .string _ => rfl
  | _, .constructor head arguments member data => by
    have inherited : portInherited head = true := by
      simp only [machineConstructors, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have notEval : head ≠ "eval" := by
      intro same
      rw [same] at member
      simp [machineConstructors] at member
    have notUnique : head ≠ "unique" := by
      intro same
      rw [same] at member
      simp [machineConstructors] at member
    have all : arguments.all (codeWithin portInherited) = true :=
      List.all_eq_true.mpr fun argument inside => machineData_within (data argument inside)
    simp [codeWithin, expressionHeadWithin, inherited, notEval, notUnique, all]

theorem port_rows (table : Table) (seeds : List Head) (ticks : Nat) (head : String)
    (port : head.startsWith "lang:compiled:" = true) :
    (portRuntime table seeds ticks).equations.filter (·.head == head) =
      (portProgram table seeds ticks).equations.filter (·.head == head) := by
  have base : runtime.equations.filter (·.head == head) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro equation member same
    have row := List.all_eq_true.mp runtime_port_free equation member
    simp only [Bool.and_eq_true] at row
    rw [beq_iff_eq.mp same] at row
    simp [portInherited, port] at row
  simp only [portRuntime, SpaceSemantics.Program.append, List.filter_append, base, List.nil_append]

/-! ## The port's three calls -/

theorem port_begin (state : State) (table : Table) (seeds : List Head) (ticks : Nat) :
    PureReturns (portRuntime table seeds ticks) [] state (apply "lang:compiled:begin" []) state
      (runAtom table (Mettapedia.Languages.CHR.Machine.start seeds)) := by
  have rows := port_rows table seeds ticks "lang:compiled:begin" (by decide +kernel)
  apply call_returns _ [] state state "lang:compiled:begin" [] _ _ _ (by decide +kernel)
  · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inr ⟨portBegin table seeds, by simp [portRuntime, SpaceSemantics.Program.append, portProgram], rfl⟩
  · apply authored_function_arguments_return _ [] [] state state "lang:compiled:begin" [] 0
      (portBegin table seeds).body _ (by decide +kernel) (by decide +kernel)
    · rw [clauses_use_only_the_named_equations, rows]
      simp [portProgram, portBegin, portAdvance, portOutcome, SpaceSemantics.matchValue.matchValues]
    · apply lift_port table seeds ticks _
        (begin_returns [] state _ _ table seeds (machineData_returns [] state (programAtom_data table))
          (machineData_returns [] state (map_data headAtom headAtom_data seeds)))
      simp only [codeWithin, expressionHeadWithin, atomsWithin, Bool.and_true, Bool.true_and]
      simp [portInherited, machineData_within (programAtom_data table),
        machineData_within (map_data headAtom headAtom_data seeds)]

theorem port_raw (table : Table) (seeds : List Head) (ticks : Nat) (head : String)
    (declared : head = "lang:compiled:advance" ∨ head = "lang:compiled:outcome") :
    argumentIsRaw (portRuntime table seeds ticks) head 0 = true := by
  have notKnown : StdLib.known head = false := by
    rcases declared with rfl | rfl <;> decide +kernel
  simp only [argumentIsRaw, notKnown, Bool.false_eq_true, ↓reduceIte, portRuntime,
    SpaceSemantics.Program.append, List.any_append, Bool.or_eq_true, List.any_eq_true]
  right
  rcases declared with rfl | rfl
  · exact ⟨arrowDeclaration "lang:compiled:advance" [.symbol "Atom", .symbol "%Undefined%"],
      by simp [portProgram], by simp [arrowDeclaration, formalArgumentIsRaw]⟩
  · exact ⟨arrowDeclaration "lang:compiled:outcome" [.symbol "Atom", .symbol "%Undefined%"],
      by simp [portProgram], by simp [arrowDeclaration, formalArgumentIsRaw]⟩

theorem port_advance (state : State) (table : Table) (seeds : List Head) (ticks : Nat) (headed : TableHeaded table)
    (machine : MachineState) (ready : Ready machine) (caller : Subst) (code : Atom)
    (captured : applySubst caller code = runAtom table machine) :
    PureReturns (portRuntime table seeds ticks) caller state (apply "lang:compiled:advance" [code]) state
      (runAtom table (Mettapedia.Languages.CHR.Machine.advance table ticks machine)) := by
  have rows := port_rows table seeds ticks "lang:compiled:advance" (by decide +kernel)
  apply raw_call_returns _ caller state state "lang:compiled:advance" [code] _ _ _ _ (by decide +kernel)
  · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inr ⟨portAdvance ticks, by simp [portRuntime, SpaceSemantics.Program.append, portProgram], rfl⟩
  · intro index bounded
    simp only [List.length_singleton, Nat.lt_one_iff] at bounded
    subst bounded
    exact port_raw table seeds ticks _ (.inl rfl)
  · simp only [List.map_cons, List.map_nil, captured, List.length_singleton]
    apply authored_function_arguments_return _ caller [("run", runAtom table machine)] state state
      "lang:compiled:advance" [runAtom table machine] 1 (portAdvance ticks).body _ (by decide +kernel) (by decide +kernel)
    · have filtered : (portRuntime table seeds ticks).equations.filter (·.head == "lang:compiled:advance") =
          [(portAdvance ticks)] := by
        rw [rows]
        simp [portProgram, portBegin, portAdvance, portOutcome]
      exact PureData.named_equation_clause _ "lang:compiled:advance" (portAdvance ticks) ["run"] [runAtom table machine]
        filtered rfl (by simp) rfl
    · apply lift_port table seeds ticks _
        (unit_returns [("run", runAtom table machine)] state (.var "run") (integer ticks) table headed machine ready
          ticks (bound_returns _ _ _ (by rfl)) (integer_returns runtime _ state ticks))
      simp [codeWithin, expressionHeadWithin, atomsWithin, portInherited, integer]

theorem port_outcome (state : State) (table : Table) (seeds : List Head) (ticks : Nat) (machine : MachineState)
    (caller : Subst) (code : Atom) (captured : applySubst caller code = runAtom table machine) :
    PureReturns (portRuntime table seeds ticks) caller state (apply "lang:compiled:outcome" [code]) state
      (resultAtom machine) := by
  have rows := port_rows table seeds ticks "lang:compiled:outcome" (by decide +kernel)
  apply raw_call_returns _ caller state state "lang:compiled:outcome" [code] _ _ _ _ (by decide +kernel)
  · simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inr ⟨portOutcome, by simp [portRuntime, SpaceSemantics.Program.append, portProgram], rfl⟩
  · intro index bounded
    simp only [List.length_singleton, Nat.lt_one_iff] at bounded
    subst bounded
    exact port_raw table seeds ticks _ (.inr rfl)
  · simp only [List.map_cons, List.map_nil, captured, List.length_singleton]
    apply authored_function_arguments_return _ caller [("run", runAtom table machine)] state state
      "lang:compiled:outcome" [runAtom table machine] 1 portOutcome.body _ (by decide +kernel) (by decide +kernel)
    · have filtered : (portRuntime table seeds ticks).equations.filter (·.head == "lang:compiled:outcome") =
          [portOutcome] := by
        rw [rows]
        simp [portProgram, portBegin, portAdvance, portOutcome]
      exact PureData.named_equation_clause _ "lang:compiled:outcome" portOutcome ["run"] [runAtom table machine]
        filtered rfl (by simp) rfl
    · apply lift_port table seeds ticks _
        (outcome_returns [("run", runAtom table machine)] state (.var "run") table machine
          (bound_returns _ _ _ (by rfl)))
      simp [codeWithin, expressionHeadWithin, atomsWithin, portInherited]

/-! ## A prepared program runs as the refined semantics -/

open Mettapedia.Languages.CHR (Constraint)

/-- **The prepared port runs the machine, and the machine runs the refined
semantics.** Over the port of a program's occurrence table and the seeds of
`constraints`, `begin` returns the start run, each `advance` moves the run
by `ticks` machine ticks, and `outcome` reports the machine's result; every
state a bounded run reaches simulates a state that the refined operational
relation reaches from `initial constraints`, with the same outcome. -/
theorem port_runs (program : Mettapedia.Languages.CHR.Program) (constraints : List Constraint) (ticks : Nat)
    (state : State) :
    PureReturns (portRuntime (Mettapedia.Languages.CHR.Machine.table program) (constraints.map Constraint.asHead)
        ticks) [] state (apply "lang:compiled:begin" []) state
      (runAtom (Mettapedia.Languages.CHR.Machine.table program)
        (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))) ∧
    (∀ (units : Nat) (caller : Subst) (code : Atom),
      applySubst caller code = runAtom (Mettapedia.Languages.CHR.Machine.table program)
        (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) (units * ticks)
          (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))) →
      PureReturns (portRuntime (Mettapedia.Languages.CHR.Machine.table program) (constraints.map Constraint.asHead)
          ticks) caller state (apply "lang:compiled:advance" [code]) state
        (runAtom (Mettapedia.Languages.CHR.Machine.table program)
          (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program)
            ((units + 1) * ticks) (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))))) ∧
    (∀ (budget : Nat) (caller : Subst) (code : Atom),
      applySubst caller code = runAtom (Mettapedia.Languages.CHR.Machine.table program)
        (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) budget
          (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))) →
      PureReturns (portRuntime (Mettapedia.Languages.CHR.Machine.table program) (constraints.map Constraint.asHead)
          ticks) caller state (apply "lang:compiled:outcome" [code]) state
        (resultAtom (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) budget
          (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead)))) ∧
      ∃ abstract, Relation.ReflTransGen (Mettapedia.Languages.CHR.Step program)
          (Mettapedia.Languages.CHR.initial constraints) abstract ∧
        Mettapedia.Languages.CHR.Machine.OutcomeRel
          (Mettapedia.Languages.CHR.Machine.outcome
            (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) budget
              (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))))
          (Mettapedia.Languages.CHR.observe abstract)) := by
  have headed := Mettapedia.Languages.CHR.Machine.table_headed program
  have startReady := Mettapedia.Languages.CHR.Machine.start_ready (constraints.map Constraint.asHead)
  refine ⟨port_begin state _ _ ticks, fun units caller code captured => ?_, fun budget caller code captured => ?_⟩
  · have advanced := port_advance state _ (constraints.map Constraint.asHead) ticks headed _
      (Mettapedia.Languages.CHR.Machine.advance_ready _ headed _ _ startReady) caller code captured
    rwa [Mettapedia.Languages.CHR.Machine.advance_add, show units * ticks + ticks = (units + 1) * ticks by ring]
      at advanced
  · refine ⟨port_outcome state _ _ ticks _ caller code captured, ?_⟩
    obtain ⟨abstract, run, _, related⟩ := Mettapedia.Languages.CHR.Machine.advance_refines program constraints budget
    exact ⟨abstract, run, related⟩

/-! ## Source text

Every machine constructor and every symbol of machine data is a symbol the
source reader keeps, so machine data renders. The machine renders, and so
does a port whose entry names are such symbols. -/

theorem machineConstructors_safe : machineConstructors.all ReadAfterRender.symbolSafe = true := by
  decide +kernel

theorem machineData_renders : ∀ {atom : Atom}, MachineData atom → (ReadAfterRender.chars? atom).isSome = true
  | _, .symbol name safe => by
    rw [ReadAfterRender.chars?_symbol]
    exact safe
  | _, .integer value => ReadAfterRender.chars?_int value
  | _, .string value => ReadAfterRender.chars?_string value
  | _, .constructor head arguments member data => by
    rw [ReadAfterRender.chars?_expression, ReadAfterRender.charsList?_isSome]
    intro item inside
    rcases List.mem_cons.mp inside with rfl | later
    · rw [ReadAfterRender.chars?_symbol]
      exact List.all_eq_true.mp machineConstructors_safe _ member
    · exact machineData_renders (data item later)

theorem machine_balanced : SpaceSemantics.Balanced CHRMachineSource.source.program := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem machine_renders : (ReadAfterRender.renderProgram? CHRMachineSource.source.program).isSome = true := by
  decide +kernel

/-- The port renders when its entry names are symbols the source reader keeps. -/
theorem portProgramFor_renders {entry : String} (table : Table) (seeds : List Head) (ticks : Nat)
    (named : ∀ suffix ∈ [":begin", ":advance", ":outcome"],
      ReadAfterRender.symbolSafe (entry ++ suffix) = true) :
    (ReadAfterRender.renderProgram? (portProgramFor entry table seeds ticks)).isSome = true := by
  have program := machineData_renders (programAtom_data table)
  have posted := machineData_renders (map_data headAtom headAtom_data seeds)
  have begin := named ":begin" (by simp)
  have advance := named ":advance" (by simp)
  have outcome := named ":outcome" (by simp)
  rw [ReadAfterRender.renderProgram?_isSome]
  intro atom member
  simp only [SpaceSemantics.loadedAtoms, SpaceSemantics.loadedAtoms.go, portProgramFor, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [SpaceSemantics.Equation.toAtom, arrowDeclaration, apply,
      WireKit.integer, ReadAfterRender.chars?_expression, ReadAfterRender.charsList?_isSome,
      ReadAfterRender.chars?_symbol, ReadAfterRender.chars?_int,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, begin, advance, outcome,
      program, posted, and_self]

#print axioms machineData_returns
#print axioms machineData_renders
#print axioms machine_renders
#print axioms portProgramFor_renders
#print axioms port_runs
#print axioms port_advance
#print axioms port_outcome
#print axioms port_begin
#print axioms programAtom_data

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
