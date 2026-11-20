import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Core

/-!
# One surface, several elaborations into the core

**The surface.** Programs are functions with an optional declaration `(: f (-> T1 .. Tn R))` and
equations `(= (f p1 .. pn) body)`. Types are `Atom`, `Proc`, `Number`, `Bool`, `%Undefined%` (also
the type of everything undeclared), a type variable, and `(Code T)` for the typed refinement. Terms
are atoms; `let`, `eval` and `+` are the special heads. A parameter whose type holds (`Atom`,
`(Code T)`) receives its argument as written; every other parameter receives the argument's value.

**A design** (`Design`) fixes six choices, and one function `elabC` elaborates every design: the
choices decide, occurrence by occurrence, whether the core term is `ret` (pass the datum) or `run`
(run the datum as code).

* `held`: where an occurrence of a held parameter runs: `never`; only when it is the whole body
  (`root`); or at every computation position (`everywhere`).
* `holdsUnderProc`: held parameters stay held under a `Proc` result while they run under the other
  computation types (the withdrawn hybrid).
* `rerunValues`: an occurrence of a value (an evaluated parameter, a `let`-bound name) at a
  computation position runs the value again.
* `atomBody`: a body under an `Atom` result is elaborated as a computation, instead of being
  returned as written.
* `constructorsRun`: the arguments of a head with no definition are computation positions.
* `reportsRefusal`: a refused result check prints as an error atom, instead of giving no answer.

**The named designs.** `he` (Hyperon Experimental), `byName`, `codeValue` (PeTTa's reading), the
withdrawn `hybrid`, and `primeToday` (the Prime draft as measured on 12 November). Each is a value
of `Design`; none has an evaluator of its own.

`elabProg` elaborates a whole program; its `code` (what `run` does to a datum) is the same
elaboration applied to the datum at a computation position, so running a quoted text and writing
it are one computation (`run_code`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core

/-- Declared types of the surface. -/
inductive Ty where
  /-- `Atom`: data, the argument as written. -/
  | atom
  /-- `Proc`: a computation. -/
  | proc
  | number
  | bool
  /-- `%Undefined%`, and every undeclared position. -/
  | undef
  /-- A type variable `$t`. -/
  | tvar
  /-- The typed refinement: code whose run yields a value of the given type. -/
  | code (result : Ty)
  deriving DecidableEq, Repr

/-- A parameter of this type receives its argument as written. -/
def Ty.holds : Ty → Bool
  | .atom => true
  | .code _ => true
  | _ => false

/-- The check a declared type makes on a value. -/
def Ty.check : Ty → Option Kind
  | .number => some .number
  | .bool => some .bool
  | _ => none

/-- A surface function: its declaration, if any, and its equations (argument patterns, body). -/
structure Fn where
  head : String
  decl : Option (List Ty × Ty)
  eqns : List (List Atom × Atom)

/-- A surface program. -/
abbrev SProg := List Fn

/-- The arity: from the declaration, else from the first equation. -/
def Fn.arity (fn : Fn) : Nat :=
  match fn.decl with
  | some (ps, _) => ps.length
  | none => (fn.eqns.head?.map fun e => e.1.length).getD 0

/-- Declared parameter types; an undeclared function's parameters are `%Undefined%`. -/
def Fn.params (fn : Fn) : List Ty :=
  match fn.decl with
  | some (ps, _) => ps
  | none => List.replicate fn.arity .undef

/-- The declared result type; `%Undefined%` when undeclared. -/
def Fn.result (fn : Fn) : Ty :=
  match fn.decl with
  | some (_, r) => r
  | none => .undef

/-- The parameter types of each head at each arity. -/
abbrev Modes := String → Nat → Option (List Ty)

/-- The modes a program declares. -/
def modesOf (P : SProg) : Modes := fun h n =>
  (P.find? fun fn => fn.head == h && fn.arity == n).map Fn.params

/-- Where an occurrence of a held parameter runs. -/
inductive HeldRule where
  | never
  | root
  | everywhere
  deriving DecidableEq, Repr

/-- A design: six choices (see the module text). -/
structure Design where
  held : HeldRule
  holdsUnderProc : Bool
  rerunValues : Bool
  atomBody : Bool
  constructorsRun : Bool
  reportsRefusal : Bool
  deriving DecidableEq, Repr

/-- Whether held parameters may run in a body under this result type. -/
def Design.heldUnder (D : Design) : Ty → Bool
  | .atom => false
  | .proc => !D.holdsUnderProc
  | _ => true

/-- Whether an occurrence of a held parameter runs, given whether held parameters may run in this
body and whether the occurrence is the whole body. -/
def heldRunsAt (D : Design) (runs isRoot : Bool) : Bool :=
  match D.held with
  | .never => false
  | .root => runs && isRoot
  | .everywhere => runs

/-- Names for the values of evaluated arguments; they start with `#`, which no surface variable
does. -/
def slot : Nat → String
  | 0 => "#0"
  | n + 1 => slot n ++ "'"

/-- The variables of a pattern. -/
def patVars : Atom → List String
  | .var x => [x]
  | .expression items => patVarsList items
  | _ => []
where
  /-- The variables of a list of patterns. -/
  patVarsList : List Atom → List String
    | [] => []
    | a :: as => patVars a ++ patVarsList as

/-- The variables that held parameters bind. -/
def heldVars : List Ty → List Atom → List String
  | p :: ps, a :: as => (if p.holds then patVars a else []) ++ heldVars ps as
  | _, _ => []

/-- An occurrence of a variable at a computation position. `heldRun isRoot` says whether a held
variable runs there. -/
def elabVar (D : Design) (held : List String) (heldRun : Bool → Bool) (isRoot : Bool)
    (x : String) : Comp :=
  if held.contains x then
    (if heldRun isRoot then .run (.var x) else .ret (.var x))
  else if D.rerunValues then .run (.var x) else .ret (.var x)

mutual
/-- Elaborate a term at a computation position. `held` lists the held variables in scope,
`heldRun isRoot` whether a held variable runs at a position that is (or is not) the whole body,
`isRoot` whether the term is the whole body. -/
def elabC (D : Design) (ms : Modes) (held : List String) (heldRun : Bool → Bool) (isRoot : Bool) :
    Atom → Comp
  | .var x => elabVar D held heldRun isRoot x
  | .expression [.symbol "let", .var y, src, body] =>
      .bind (elabC D ms held heldRun false src) y (elabC D ms (held.erase y) heldRun false body)
  | .expression [.symbol "eval", m] =>
      .bind (elabC D ms held heldRun false m) "#e" (.run (.var "#e"))
  | .expression [.symbol "+", a, b] =>
      .bind (elabC D ms held heldRun false a) (slot 0)
        (.bind (elabC D ms held heldRun false b) (slot 1)
          (.plus (.var (slot 0)) (.var (slot 1))))
  | .expression (.symbol h :: args) =>
      match ms h args.length with
      | some ps => elabArgs D ms held heldRun ps args 0 [] (.call h)
      | none =>
          if D.constructorsRun then
            elabArgs D ms held heldRun (List.replicate args.length .undef) args 0 []
              fun items => .ret (.expression (.symbol h :: items))
          else .ret (.expression (.symbol h :: args))
  | a => .ret a

/-- Elaborate the arguments of a head: an argument at a held position is passed as written, every
other one is run first and its value passed. -/
def elabArgs (D : Design) (ms : Modes) (held : List String) (heldRun : Bool → Bool) :
    List Ty → List Atom → Nat → List Atom → (List Atom → Comp) → Comp
  | p :: ps, a :: as, i, acc, k =>
      if p.holds then elabArgs D ms held heldRun ps as (i + 1) (acc ++ [a]) k
      else
        .bind (elabC D ms held heldRun false a) (slot i)
          (elabArgs D ms held heldRun ps as (i + 1) (acc ++ [.var (slot i)]) k)
  | _, _, _, acc, k => k acc
end

/-- A body under its declared result type. -/
def elabBody (D : Design) (ms : Modes) (held : List String) (R : Ty) (body : Atom) : Comp :=
  match R with
  | .atom => if D.atomBody then elabC D ms held (heldRunsAt D false) true body else .ret body
  | _ => elabC D ms held (heldRunsAt D (D.heldUnder R)) true body

/-- A function's definition in the core. -/
def elabFn (D : Design) (ms : Modes) (fn : Fn) : Def where
  head := fn.head
  arity := fn.arity
  argChecks := fn.params.map Ty.check
  resultCheck := fn.result.check
  clauses := fn.eqns.map fun e => (e.1, elabBody D ms (heldVars fn.params e.1) fn.result e.2)

/-- A term at the top level (a `!` query); no variable is held there. -/
def elabQuery (D : Design) (ms : Modes) : Atom → Comp :=
  elabC D ms [] (fun _ => false) false

/-- A whole program; running a datum elaborates it as a query. -/
def elabProg (D : Design) (P : SProg) : Prog where
  defs := P.map (elabFn D (modesOf P))
  code := elabQuery D (modesOf P)

/-- The answers of a query, at a fuel, as the design prints them. -/
def answers (D : Design) (P : SProg) (fuel : Nat) (q : Atom) : Option (List Atom) :=
  (exec (elabProg D P) fuel (.comp [] (elabQuery D (modesOf P) q))).map
    (observe D.reportsRefusal)

/-- Running a datum is elaborating it as a query. -/
theorem run_code (D : Design) (P : SProg) (n : Nat) (ρ : Env) (t : Atom) :
    exec (elabProg D P) (n + 1) (.comp ρ (.run t)) =
      exec (elabProg D P) n (.comp [] (elabQuery D (modesOf P) (inst ρ t))) := rfl

/-! ## The named designs -/

/-- Hyperon Experimental: held text runs wherever it lands, and so do values. -/
def he : Design :=
  { held := .everywhere, holdsUnderProc := false, rerunValues := true, atomBody := false,
    constructorsRun := true, reportsRefusal := true }

/-- By-name: held text runs at every computation position; a value never runs again. -/
def byName : Design :=
  { held := .everywhere, holdsUnderProc := false, rerunValues := false, atomBody := false,
    constructorsRun := true, reportsRefusal := true }

/-- Code value: held text is inert data everywhere; only `eval` runs it. -/
def codeValue : Design :=
  { held := .never, holdsUnderProc := false, rerunValues := false, atomBody := false,
    constructorsRun := true, reportsRefusal := false }

/-- The Prime draft as measured: a held parameter runs only as the whole body under a result other
than `Atom`; bodies under an `Atom` result are evaluated. -/
def primeToday : Design :=
  { held := .root, holdsUnderProc := false, rerunValues := false, atomBody := true,
    constructorsRun := true, reportsRefusal := true }

/-- The withdrawn hybrid: the Prime draft, holding under `Proc` as under `Atom`. -/
def hybrid : Design := { primeToday with holdsUnderProc := true }

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
