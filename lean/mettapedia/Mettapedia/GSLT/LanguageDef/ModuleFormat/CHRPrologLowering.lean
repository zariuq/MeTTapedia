import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax
import Mettapedia.Logic.Prolog.ReaderTerm
import Mettapedia.Logic.LP.TermEquality
import Mettapedia.Languages.CHR.Admission
import Mettapedia.Languages.CHR.Instantiation
import Mettapedia.Data.List.IndexAllocation

/-! Interpret Prolog sentence data into ground CHR's independent IR. Rule
sourceVariables have a local allocation; neither source names nor source terms
execute as MeTTa code. Declarations, rules and explicit ground queries are
separate source forms. Host Prolog clauses and arbitrary directives are not
implicitly turned into CHR constraints or executed by the frontend. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering

open Mettapedia.Logic.Prolog
open Mettapedia.Languages
abbrev SourceTerm := SourceSignature.Term
abbrev Variable := SourceSignature.Variable
abbrev Allocation := List (Variable × Nat)
abbrev Lower := Except String

def application? : SourceTerm → Option (String × List SourceTerm)
  | .const (.atom name) => some (name, [])
  | .app symbol arguments => some (symbol.name, List.ofFn arguments)
  | _ => none

def sourceVariables : SourceTerm → List Variable
  | .var sourceVar => [sourceVar]
  | .const _ => []
  | .app symbol arguments => (List.finRange symbol.arity).flatMap fun i => sourceVariables (arguments i)

/-- Canonical printer names can retain arbitrary IR indices. The preferred
allocation is used only for a whole scope with distinct canonical indices;
mixed names and anonymous occurrences receive ordinary fresh indices. -/
def preferredIndex? (sourceVar : Variable) : Option Nat := do
  if !sourceVar.spelling.startsWith "V" then none else do
    let index ← (sourceVar.spelling.drop 1).toString.toNat?
    if sourceVar.spelling == "V" ++ toString index then some index else none

def allocate (source : SourceTerm) : Allocation :=
  List.IndexAllocation.allocate (sourceVariables source) preferredIndex?

def index? (allocation : Allocation) (sourceVar : Variable) : Option Nat :=
  allocation.lookup sourceVar

def term (allocation : Allocation) : SourceTerm → Lower CHR.Term
  | .var sourceVar => do
      let some index := index? allocation sourceVar | .error "source variable is outside its rule scope"
      pure (.var index)
  | .const (.integer number) => pure (.value (.integer number))
  | .const (.atom name) => pure (.value (.atom name))
  | .app symbol arguments =>
      if symbol.name == "tuple" then
        CHR.Term.tuple <$> (List.finRange symbol.arity).mapM (fun i => term allocation (arguments i))
      else .error "C0 compound values use tuple(...)"
  | _ => .error "C0 values are integers, atoms and tuples"

def head (allocation : Allocation) (source : SourceTerm) : Lower CHR.Head := do
  let some (name, arguments) := application? source | .error "expected a CHR constraint"
  pure ⟨name, ← arguments.mapM (term allocation)⟩

def intOperator? : String → Option CHR.IntOperator
  | "+" => some .add | "-" => some .subtract | "*" => some .multiply
  | "//" => some .quotient | "rem" => some .remainder | "mod" => some .modulo
  | _ => none

def expression (allocation : Allocation) : SourceTerm → Lower CHR.IntExpr
  | .const (.integer number) => pure (.literal number)
  | .var sourceVar => do
      let some index := index? allocation sourceVar | .error "arithmetic variable is outside its rule scope"
      pure (.index index)
  | .app symbol arguments => do
      if unary : symbol.arity = 1 then
        if symbol.name == "-" then
          pure (.operation .subtract (.literal 0) (← expression allocation (arguments ⟨0, by change 0 < symbol.arity; omega⟩)))
        else if symbol.name == "+" then expression allocation (arguments ⟨0, by change 0 < symbol.arity; omega⟩)
        else .error "unsupported C0 unary integer operation"
      else if binary : symbol.arity = 2 then
        let some operator := intOperator? symbol.name | .error "unsupported C0 integer operation"
        pure (.operation operator (← expression allocation (arguments ⟨0, by change 0 < symbol.arity; omega⟩))
          (← expression allocation (arguments ⟨1, by change 1 < symbol.arity; omega⟩)))
      else .error "invalid C0 arithmetic arity"
  | _ => .error "C0 arithmetic requires an integer expression"

def comparison? : String → Option CHR.Comparison
  | "=:=" => some .equal | "=\\=" => some .different | "<" => some .less
  | "=<" => some .lessEqual | ">" => some .greater | ">=" => some .greaterEqual
  | _ => none

def guard (allocation : Allocation) (source : SourceTerm) : Lower CHR.Guard := do
  let some (name, [left, right]) := application? source | .error "expected a C0 guard test"
  if name == "==" then pure (.identical (← term allocation left) (← term allocation right))
  else if name == "\\==" then pure (.distinct (← term allocation left) (← term allocation right))
  else
    let some operator := comparison? name | .error "unsupported C0 guard test"
    pure (.compare operator (← expression allocation left) (← expression allocation right))

def conjunction : SourceTerm → List SourceTerm
  | source@(.app symbol arguments) =>
      if paired : symbol.name = "," ∧ symbol.arity = 2 then
        conjunction (arguments ⟨0, by change 0 < symbol.arity; omega⟩) ++ conjunction (arguments ⟨1, by change 1 < symbol.arity; omega⟩)
      else [source]
  | source => [source]

def guards (allocation : Allocation) (source : SourceTerm) : Lower (List CHR.Guard) :=
  ((conjunction source).filter (· != SourceSignature.atom "true")).mapM (guard allocation)

def goal (allocation : Allocation) (source : SourceTerm) : Lower CHR.Goal := do
  if source = SourceSignature.atom "fail" then pure .fail
  else match application? source with
    | some ("is", [.var sourceVar, right]) =>
        let some index := index? allocation sourceVar | .error "assignment variable is outside its rule scope"
        pure (.assign index (← expression allocation right))
    | some ("is", [_, _]) => .error "C0 assignments require a variable on the left of is"
    | _ => CHR.Goal.tell <$> head allocation source

def goals (allocation : Allocation) (source : SourceTerm) : Lower (List CHR.Goal) :=
  ((conjunction source).filter (· != SourceSignature.atom "true")).mapM (goal allocation)

def heads (allocation : Allocation) (source : SourceTerm) : Lower (List CHR.Head) :=
  (conjunction source).mapM (head allocation)

def rule (ordinal : Nat) (source : SourceTerm) : Lower CHR.Rule := do
  let allocation := allocate source
  let (name, body) ← match application? source with
    | some ("@", [.const (.atom name), body]) => pure (name, body)
    | some ("@", _) => .error "CHR rule names must be atoms"
    | _ => pure ("rule:" ++ toString ordinal, source)
  let some (kind, [left, right]) := application? body | .error "expected a CHR rule"
  let (kept, removed) ← if kind == "==>" then pure (← heads allocation left, [])
    else if kind == "<=>" then match application? left with
      | some ("\\", [kept, removed]) => pure (← heads allocation kept, ← heads allocation removed)
      | _ => pure ([], ← heads allocation left)
    else .error "expected <=> or ==>"
  let (guarded, body) ← match application? right with
    | some ("|", [guarded, body]) => pure (← guards allocation guarded, body)
    | _ => pure ([], right)
  pure ⟨name, kept, removed, guarded, ← goals allocation body⟩

def declaration (source : SourceTerm) : Lower CHR.Declaration := do
  let some ("/", [.const (.atom name), .const (.integer arity)]) := application? source
    | .error "expected a constraint name/arity declaration"
  if arity < 0 then .error "constraint arity must be nonnegative" else pure ⟨name, arity.toNat⟩

def groundConstraint (source : SourceTerm) : Lower CHR.Constraint := do
  let head ← head [] source
  let some constraint := head.instantiate [] | .error "initial C0 queries must be ground"
  pure constraint

inductive Form where
  | declarations (values : List CHR.Declaration)
  | rule (value : CHR.Rule)
  | query (values : List CHR.Constraint)
  | metadata
  deriving Repr, DecidableEq

def form (ordinal : Nat) (source : SourceTerm) : Lower Form := do
  match application? source with
  | some (":-", [directive]) =>
      match application? directive with
      | some ("chr_constraint", [declarations]) =>
          Form.declarations <$> (conjunction declarations).mapM declaration
      | some ("use_module", [library]) =>
          if application? library = some ("library", [SourceSignature.atom "chr"]) then pure .metadata
          else .error "C0 does not execute host module imports"
      | some ("chr_option", [mode, value]) =>
          if mode = SourceSignature.atom "optimize" ∧ value = SourceSignature.atom "off" then pure .metadata
          else .error "C0 uses its declared refined execution profile"
      | some ("set_prolog_flag", [flag, mode]) =>
          if flag = SourceSignature.atom "double_quotes" ∧ mode = SourceSignature.atom "atom" then pure .metadata
          else if flag = SourceSignature.atom "double_quotes" then
            .error "C0 reads double-quoted text as atoms; other double_quotes modes need value kinds C0 does not have"
          else .error "unsupported C0 source flag"
      | _ => .error "unsupported C0 source directive"
  | some ("?-", [query]) => Form.query <$> (conjunction query).filterMapM fun source => do
      if source = SourceSignature.atom "true" then pure none else some <$> groundConstraint source
  | _ => Form.rule <$> rule ordinal source

structure Program where
  program : CHR.Program
  inputs : List CHR.Constraint
  deriving Repr, DecidableEq

def assemble (forms : List Form) : Lower Program := do
  let declarations := forms.flatMap fun form => match form with | .declarations rows => rows | _ => []
  let rules := forms.filterMap fun form => match form with | .rule rule => some rule | _ => none
  let inputs := forms.flatMap fun form => match form with | .query rows => rows | _ => []
  let program : CHR.Program := ⟨declarations, rules⟩
  unless inputs.all (fun constraint => CHR.Admission.declared program
      ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩) do
    .error "initial C0 constraint has no matching name/arity declaration"
  match CHR.Admission.diagnose program with
  | some reason => .error s!"C0 admission refused: {reprStr reason}"
  | none => pure ⟨program, inputs⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
