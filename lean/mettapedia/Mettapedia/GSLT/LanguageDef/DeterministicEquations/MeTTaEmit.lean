import Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData

/-!
# Emission of computational equations into ordered MeTTa dispatchers

Each source head becomes one equation over an encoded argument vector.
Minimal `function`, `chain`, `unify` and `eval` instructions retain source
priority without duplicating continuations. Explicit outcomes and fresh target
variables separate failure, exhaustion, data and lexical binding. This emitter
is executable; complete target-evaluation and textual correspondence remain
separate obligations. OrderedDispatch establishes only its selection component.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def sequenceAtom : List Atom → Atom
  | [] => .symbol "nik:Nil"
  | first :: rest => call "nik:Cons" [first, sequenceAtom rest]

/-- Print generated atoms, using MeTTa string escapes for their payloads.
The data encoder produces only symbols, strings and expressions. -/
def render : Atom → String
  | .symbol name => name
  | .var name => "$" ++ name
  | .grounded (.string text) => text.quote
  | .grounded value => value.toString
  | .expression items => "(" ++ String.intercalate " " (items.map render) ++ ")"

def data (term : Term) : String := render (MeTTaData.encode term)

def dataItems (items : List Term) : String := render (MeTTaData.encodeItems items)

def value (payload : Atom) : Atom := call "nik:Value" [payload]

def dispatchName (head : String) : String :=
  "nik:call:" ++ String.join (head.toUTF8.data.toList.map fun byte =>
    let digits := String.ofList (Nat.toDigits 16 byte.toNat)
    if byte.toNat < 16 then "0" ++ digits else digits)

def primitiveHeads : List String :=
  ["nik:nat-zero", "nik:nat-pred", "nik:nat-add", "nik:nat-monus",
   "nik:nat-max", "nik:nat-le", "nik:nat-lt", "nik:nat-eq",
   "nik:nat-mul", "nik:nat-div", "nik:nat-mod", "nik:list-view",
   "nik:list-cons", "nik:data-eq"]

abbrev Names := List (String × Atom)
abbrev Emit := StateM Nat

def fresh : Emit Atom := do
  let index ← get
  set (index + 1)
  pure (.var ("nik" ++ toString index))

mutual

def pattern (term : Term) : Emit (Atom × Names) :=
  match term with
  | .var name => do
      let target ← fresh
      pure (target, [(name, target)])
  | .expr items => do
      let (rendered, names) ← patterns items
      pure (call "nik:Expr" [rendered], names)
  | .list items => do
      let (rendered, names) ← patterns items
      pure (call "nik:List" [rendered], names)
  | atom => pure (MeTTaData.encode atom, [])

def patterns : List Term → Emit (Atom × Names)
  | [] => pure (.symbol "nik:Nil", [])
  | first :: rest => do
      let (head, headNames) ← pattern first
      let (tail, tailNames) ← patterns rest
      pure (call "nik:Cons" [head, tail], headNames ++ tailNames)

end

def returned (atom : Atom) : Atom := call "return" [atom]

/-- A first-match scan; a selected body's result never retries later rows. -/
def selectBranches (target : Atom) (branches : List (Atom × Atom)) (otherwise : Atom) : Atom :=
  branches.foldr (fun (left, right) rest => call "unify" [target, left, right, rest]) otherwise

/-- Inspect a computed operand, propagating each non-value outcome. -/
def resultBranches (result name continuation : Atom) : Atom :=
  selectBranches result
    [(value name, continuation),
     (.symbol "nik:Failure", returned (.symbol "nik:Failure")),
     (.symbol "nik:Exhausted", returned (.symbol "nik:Exhausted"))]
    (returned (.symbol "nik:Malformed"))

def bindResult (expression name continuation : Atom) : Emit Atom := do
  let result ← fresh
  pure (call "chain" [call "function" [expression], result,
    resultBranches result name continuation])

def invoke (program : Program) (fuel : Atom) (head : String)
    (arguments : List Atom) : Atom :=
  if program.defines head then call (dispatchName head) [fuel, sequenceAtom arguments]
  else if head ∈ primitiveHeads then
    call "nik:primitive" [.grounded (.string head), sequenceAtom arguments]
  else value (call "nik:Expr" [sequenceAtom (MeTTaData.encode (.sym head) :: arguments)])

def returnInvocation (invocation : Atom) : Emit Atom := do
  match invocation with
  | .expression [.symbol "nik:Value", _] => pure (returned invocation)
  | .expression (.symbol "nik:primitive" :: _) =>
      let context ← fresh
      let result ← fresh
      pure (call "chain" [call "context-space" [], context,
        call "chain" [call "metta" [invocation, .symbol "%Undefined%", context], result,
          returned result]])
  | _ =>
      let result ← fresh
      pure (call "chain" [call "eval" [invocation], result, returned result])

/-- Allocate the remaining-fuel variable and guard one source evaluation step. -/
def withFuel (fuel : Atom) (build : Atom → Emit Atom) : Emit Atom := do
  let remaining ← fresh
  let body ← build remaining
  let exhausted ← fresh
  pure (call "chain" [call "eval" [call "==" [fuel, .grounded (.int 0)]], exhausted,
    call "unify" [exhausted, .grounded (.bool true), returned (.symbol "nik:Exhausted"),
      call "chain" [call "eval" [call "-" [fuel, .grounded (.int 1)]], remaining, body]]])

mutual

def expression (program : Program) (names : Names) (fuel : Atom)
    (term : Term) : Emit Atom :=
  withFuel fuel fun remaining => match term with
    | .var name => pure (returned (match names.find? (fun entry => entry.1 == name) with
        | some (_, target) => value target
        | none => .symbol "nik:Failure"))
    | .sym _ | .lit _ | .expr [] => pure (returned (value (MeTTaData.encode term)))
    | .list terms => expressions program names remaining terms
        (fun items => pure (returned (value (call "nik:List" [sequenceAtom items]))))
    | .expr [.sym "let", .var name, bound, body] => do
        let target ← fresh
        let assigned ← expression program names remaining bound
        let body ← expression program ((name, target) :: names) remaining body
        bindResult assigned target body
    | .expr [.sym "let", _, _, _] => pure (returned (.symbol "nik:Failure"))
    | .expr [.sym "metta-nullary", .sym name] =>
        pure (returned (value (MeTTaData.encode (.expr [.sym name]))))
    | .expr [.sym "metta-nullary", _] => pure (returned (.symbol "nik:Failure"))
    | .expr (.sym head :: terms) => expressions program names remaining terms
        (fun arguments => returnInvocation (invoke program remaining head arguments))
    | .expr terms => expressions program names remaining terms
        (fun items => pure (returned (value (call "nik:Expr" [sequenceAtom items]))))
termination_by sizeOf term

def expressions (program : Program) (names : Names) (fuel : Atom)
    (terms : List Term) (continuation : List Atom → Emit Atom) : Emit Atom :=
  match terms with
  | [] => continuation []
  | first :: rest => do
      let target ← fresh
      let head ← expression program names fuel first
      let tail ← expressions program names fuel rest (fun values => continuation (target :: values))
      bindResult head target tail
termination_by sizeOf terms

end

def dispatcher (program : Program) (head : String) : Emit (Atom × Atom) := do
  let fuel ← fresh
  let arguments ← fresh
  let mut branches : List (Atom × Atom) := []
  for row in OrderedDispatch.compileHead program head do
    let (left, names) ← patterns row.equation.params
    let right ← expression program names fuel row.equation.body
    branches := branches ++ [(left, right)]
  let checked ← fresh
  let body := call "chain" [arguments, checked,
    selectBranches checked branches
      (returned (.symbol "nik:Failure"))]
  pure (call ":" [.symbol (dispatchName head),
      call "->" [.symbol "Number", .symbol "Atom", .symbol "%Undefined%"]],
    call "=" [call (dispatchName head) [fuel, arguments], call "function" [body]])

/-- Actual target syntax: one type declaration and equation per source head. -/
def programAtoms (source : Program) : List (Atom × Atom) :=
  ((source.map Equation.head).eraseDups.mapM (dispatcher source)).run' 0

/-- Compile every source head, preserving each head's original ordered rows. -/
def program (source : Program) : String :=
  String.intercalate "\n\n"
    ((programAtoms source).map fun (annotation, equation) =>
      render annotation ++ "\n" ++ render equation) ++ "\n"

/-- A closed, already encoded argument request; argument data is never evaluated as code. -/
def requestAtom (source : Program) (fuel : Nat) (head : String) (arguments : List Term) : Atom :=
  invoke source (.grounded (.int fuel)) head (arguments.map MeTTaData.encode)

def request (source : Program) (fuel : Nat) (head : String) (arguments : List Term) : String :=
  render (requestAtom source fuel head arguments)

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
