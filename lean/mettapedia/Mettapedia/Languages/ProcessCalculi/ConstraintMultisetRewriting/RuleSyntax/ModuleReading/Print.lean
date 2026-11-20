import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Reading

/-!
# The reading printed as the library prints it

`readingText` prints the rules of a module's reading in the text `tcalc:module-text` of
`lib/tcalc_modules.metta` produces, one rule per line:

    (rule NAME (read R1 .. Rk) (make W1 .. Wm))

A variable `v` prints as `$v`; a constructor, relation or head application as `(f a1 .. an)`, `(f)`
with no argument; the stage head of rule `l` at index `i` as `l/i`. The text printed is that of the
rules themselves (`Rule.body.read`, `Rule.body.produce`), each under the name the reading gives it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term)
open OneFrame (Terms)

universe u

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}

/-- How to print a module's symbols. -/
structure Names (σ : LPSignature.{u, u, u, u}) (L : Type u) where
  con : σ.functionSymbols → String
  rel : σ.relationSymbols → String
  const : σ.constants → String
  var : σ.vars → String
  label : L → String

variable (names : Names σ L)

/-- The text of a head. -/
def Names.head : Head σ.functionSymbols σ.relationSymbols L → String
  | .con f => names.con f
  | .rel r => names.rel r
  | .demand => "demand"
  | .value => "value"
  | .stage l i => names.label l ++ "/" ++ toString i

/-- The text of a term (`tcalc-module:text`). -/
def Names.term : Term (readingSignature σ L) → String
  | .var v => "$" ++ names.var v
  | .const c => names.const c
  | .app f args => "(" ++ names.head f ++ String.join (List.ofFn fun i => " " ++ Names.term (args i)) ++ ")"

/-- The name of a rule of the reading. -/
def Names.rule : ReadName L → String
  | .ask l i => names.label l ++ "/" ++ toString i ++ ".ask"
  | .step l i => names.label l ++ "/" ++ toString i
  | .final l => names.label l

/-- Terms separated by spaces. -/
def Names.terms (ts : List (Term (readingSignature σ L))) : String :=
  " ".intercalate (ts.map names.term)

/-- One rule of the reading, as a line. -/
def Names.ruleLine (name : ReadName L) (rule : Rule (Terms (Term (readingSignature σ L)))) : String :=
  "(rule " ++ names.rule name ++ " (read " ++ names.terms rule.body.read ++ ") (make " ++
    names.terms rule.body.produce ++ "))\n"

/-- The rules of a module's reading, in the order `labels` gives, as the library prints them. -/
def readingText (M : L → ModuleRule (readingSignature σ L)) (labels : List L) : String :=
  String.join ((readingList M labels).map fun named => names.ruleLine named.1 named.2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
