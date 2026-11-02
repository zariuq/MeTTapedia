import Mettapedia.Languages.MeTTa.PeTTa.BetaInlining

/-!
# Controls for beta inlining

Kernel-checked runs of the machine of `Eval` on small programs.

Positive controls: the premises of `BetaInlining.Inlinable` hold for a one-equation
function and for the layer-freshness function of a breadth-first search, whose
inlined body is its own text; the call and its inlined body give the same answers;
a recursive function unfolds once; a declared literal `Atom` domain leaves a
variable argument unchanged.

Negative controls, each the failure of one premise:

* a second equation: the call also answers with the other body;
* an unbound argument variable that the body binds again: the call tests the
  captured variable and gives no answer, the inlined body binds it;
* a nondeterministic argument expression substituted for its parameter: evaluated
  once per answer by the call, at each occurrence by the substitution;
* a call of another arity runs no body: too many arguments are an
  over-application fault, too few the partial application;
* a computed argument under a literal `Atom` domain stays source.

Two behaviours of this machine are recorded: an equation added at run time is a
stored row and does not define the function, and an equation whose argument list
reads as a `cons` pattern is not selected by a call with fewer arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInliningControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval
open DeclarativeSpec (Runs)
open BetaInlining
open Mettapedia.Languages.MeTTa.TypeSchemeActivation (rename)

def answersOf : Outcome → Option (List Atom)
  | .complete _ answers [] [] => some answers
  | _ => none

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-! ## The premises hold -/

/-- `(= (f $x) (a $x))`, one equation. -/
def oneEquation : Program where
  equations := [⟨"f", [.var "x"], call "a" [.var "x"]⟩]
  declarations := []

theorem one_equation_inlinable :
    Inlinable oneEquation "f" ["x"] ["y"] (call "a" [.var "x"]) (fun _ => "y")
      [("y", int 1)] where
  single := rfl
  distinct := by simp
  closed := by
    intro x member
    simpa [call, Mettapedia.Languages.MeTTa.TypeSchemeActivation.freeVars] using member
  saturated := rfl
  renamed := by
    intro i h₁ h₂
    match i, h₁ with
    | 0, _ => rfl
  notPrimitive := by decide
  notIO := by decide
  ordinary := by decide
  bound := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨int 1, rfl⟩

/-- The theorem applied: the call `(f $y)` and its inlined body `(a $y)` complete alike. -/
theorem one_equation_beta (after : Effects.State) (answers input output : List Atom) :
    Runs oneEquation (callConfiguration "f" ["y"] [("y", int 1)] Effects.empty [] [] [])
        (.complete after answers input output) ↔
      Runs oneEquation (inlinedConfiguration (call "a" [.var "x"]) (fun _ => "y")
        [("y", int 1)] Effects.empty [] [] []) (.complete after answers input output) :=
  beta_complete Effects.empty [] [] [] one_equation_inlinable after answers input output

/-- The layer-freshness function of a breadth-first search over a state graph, its
layer space passed as a parameter:
`(= (fresh $L $km $t $N) (if (== (collapse (match $L (layer $km $t) t)) ()) (add-atom $N $t) done))`. -/
def freshBody : Atom :=
  call "if" [call "==" [call "collapse" [call "match" [.var "L",
      call "layer" [.var "km", .var "t"], sym "t"]], .expression []],
    call "add-atom" [.var "N", .var "t"], sym "done"]

def freshProgram : Program where
  equations := [⟨"fresh", [.var "L", .var "km", .var "t", .var "N"], freshBody⟩]
  declarations := []

/-- Every caller environment binding the four argument variables meets the premises,
and the inlined body is the body itself, the call passing the parameters' own names. -/
theorem fresh_inlinable (caller : Subst)
    (bound : ∀ a ∈ ["L", "km", "t", "N"], ∃ value, Subst.lookup caller a = some value) :
    Inlinable freshProgram "fresh" ["L", "km", "t", "N"] ["L", "km", "t", "N"] freshBody id
      caller where
  single := rfl
  distinct := by decide
  closed := by
    intro x member
    simp [freshBody, call, sym, Mettapedia.Languages.MeTTa.TypeSchemeActivation.freeVars] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  saturated := rfl
  renamed := fun _ _ _ => rfl
  notPrimitive := by decide
  notIO := by decide
  ordinary := by decide
  bound := bound

theorem fresh_inlined_is_body : rename id freshBody = freshBody :=
  Mettapedia.Languages.MeTTa.TypeSchemeActivation.rename_id freshBody

/-! ## Positive controls by execution -/

theorem one_equation_call : answersOf (evaluate oneEquation 64 Effects.empty
    (call "let" [.var "y", int 1, call "f" [.var "y"]])) = some [call "a" [int 1]] := by
  decide +kernel

theorem one_equation_inlined : answersOf (evaluate oneEquation 64 Effects.empty
    (call "let" [.var "y", int 1, call "a" [.var "y"]])) = some [call "a" [int 1]] := by
  decide +kernel

/-- `(= (down $x) (if (== $x 0) done (down (- $x 1))))`: recursive, one equation. -/
def countdown : Program where
  equations := [⟨"down", [.var "x"], call "if" [call "==" [.var "x", int 0], sym "done",
    call "down" [call "-" [.var "x", int 1]]]⟩]
  declarations := []

/-- One unfolding of a recursive call: `(let $y 2 (down $y))` and its inlined body both
give `done`. -/
theorem recursive_call : answersOf (evaluate countdown 128 Effects.empty
    (call "let" [.var "y", int 2, call "down" [.var "y"]])) = some [sym "done"] := by
  decide +kernel

theorem recursive_inlined : answersOf (evaluate countdown 128 Effects.empty
    (call "let" [.var "y", int 2, call "if" [call "==" [.var "y", int 0], sym "done",
      call "down" [call "-" [.var "y", int 1]]]])) = some [sym "done"] := by
  decide +kernel

/-- `(: k (-> Atom Atom))` and `(= (k $x) (quote $x))`. -/
def declaredAtom : Program where
  equations := [⟨"k", [.var "x"], call "quote" [.var "x"]⟩]
  declarations := [call ":" [sym "k", call "->" [sym "Atom", sym "Atom"]]]

/-- A declared `Atom` domain leaves a variable argument as it is:
`(let $y (p 1) (k $y))` and `(let $y (p 1) (quote $y))` both give `(p 1)`. -/
theorem declared_atom_call : answersOf (evaluate declaredAtom 64 Effects.empty
    (call "let" [.var "y", call "p" [int 1], call "k" [.var "y"]])) =
      some [call "p" [int 1]] := by
  decide +kernel

theorem declared_atom_inlined : answersOf (evaluate declaredAtom 64 Effects.empty
    (call "let" [.var "y", call "p" [int 1], call "quote" [.var "y"]])) =
      some [call "p" [int 1]] := by
  decide +kernel

/-! ## Negative controls -/

/-- `(= (f $x) (a $x)) (= (f $x) (b $x))`. -/
def twoEquations : Program where
  equations := [⟨"f", [.var "x"], call "a" [.var "x"]⟩, ⟨"f", [.var "x"], call "b" [.var "x"]⟩]
  declarations := []

/-- A second equation: the call gives `(a 1) (b 1)`, the first body alone `(a 1)`. -/
theorem second_equation_call : answersOf (evaluate twoEquations 64 Effects.empty
    (call "let" [.var "y", int 1, call "f" [.var "y"]])) =
      some [call "a" [int 1], call "b" [int 1]] := by
  decide +kernel

theorem second_equation_inlined : answersOf (evaluate twoEquations 64 Effects.empty
    (call "let" [.var "y", int 1, call "a" [.var "y"]])) = some [call "a" [int 1]] := by
  decide +kernel

/-- `(= (g $x) (let $x 5 $x))`: the body binds its parameter again. -/
def rebinding : Program where
  equations := [⟨"g", [.var "x"], call "let" [.var "x", int 5, .var "x"]⟩]
  declarations := []

/-- An unbound argument variable: `(g $u)` gives no answer, since the body tests the
captured `$u` against 5, while `(let $u 5 $u)` binds `$u` and gives 5. -/
theorem unbound_argument_call : answersOf (evaluate rebinding 64 Effects.empty
    (call "g" [.var "u"])) = some [] := by
  decide +kernel

theorem unbound_argument_inlined : answersOf (evaluate rebinding 64 Effects.empty
    (call "let" [.var "u", int 5, .var "u"])) = some [int 5] := by
  decide +kernel

/-- The same function with a bound argument: `(let $u 5 (g $u))` and
`(let $u 5 (let $u 5 $u))` both give 5. -/
theorem bound_argument_call : answersOf (evaluate rebinding 64 Effects.empty
    (call "let" [.var "u", int 5, call "g" [.var "u"]])) = some [int 5] := by
  decide +kernel

theorem bound_argument_inlined : answersOf (evaluate rebinding 64 Effects.empty
    (call "let" [.var "u", int 5, call "let" [.var "u", int 5, .var "u"]])) =
      some [int 5] := by
  decide +kernel

/-- `(= (dup $x) ($x $x))`. -/
def duplicate : Program where
  equations := [⟨"dup", [.var "x"], .expression [.var "x", .var "x"]⟩]
  declarations := []

/-- A nondeterministic argument expression: the call evaluates it once and runs the
body per answer, `(1 1) (2 2)`; substituted for the parameter, it is evaluated at each
occurrence, `(1 1) (1 2) (2 1) (2 2)`. -/
theorem nondeterministic_argument_call : answersOf (evaluate duplicate 64 Effects.empty
    (call "dup" [call "superpose" [.expression [int 1, int 2]]])) =
      some [.expression [int 1, int 1], .expression [int 2, int 2]] := by
  decide +kernel

theorem nondeterministic_argument_substituted : answersOf (evaluate duplicate 64 Effects.empty
    (.expression [call "superpose" [.expression [int 1, int 2]],
      call "superpose" [.expression [int 1, int 2]]])) =
      some [.expression [int 1, int 1], .expression [int 1, int 2],
        .expression [int 2, int 1], .expression [int 2, int 2]] := by
  decide +kernel

/-- A call of another arity runs no body: `(f 1 2)` is an over-application fault and
`(f)` is the partial application `(partial f ())`. -/
theorem arity_mismatch_call :
    (match evaluate oneEquation 64 Effects.empty (call "f" [int 1, int 2]) with
      | .fault reason _ => some reason
      | _ => none) = some (.overApplication "f" [1] 2) ∧
    answersOf (evaluate oneEquation 64 Effects.empty (call "f" [])) =
      some [partialValue "f" []] := by
  decide +kernel

/-- A computed argument under a literal `Atom` domain: `(k (+ 1 2))` keeps the source
`(+ 1 2)`, where evaluating the argument first would give `3`. -/
theorem declared_atom_keeps_source : answersOf (evaluate declaredAtom 64 Effects.empty
    (call "k" [call "+" [int 1, int 2]])) = some [call "+" [int 1, int 2]] := by
  decide +kernel

/-! ## Two behaviours of the machine -/

/-- An equation added at run time is a stored row: after
`(add-atom &self (= (f $x) (b $x)))`, `(f 1)` still gives only `(a 1)`. -/
theorem added_equation_is_inert : answersOf (evaluate oneEquation 64 Effects.empty
    (call "let" [.var "done", call "add-atom" [sym "&self",
        call "=" [call "f" [.var "x"], call "b" [.var "x"]]],
      call "f" [int 1]])) = some [call "a" [int 1]] := by
  decide +kernel

/-- `(= (h cons $a $b) $b)`: three head arguments that read as a `cons` pattern. -/
def consHead : Program where
  equations := [⟨"h", [.symbol "cons", .var "a", .var "b"], .var "b"⟩]
  declarations := []

/-- The argument list is matched element by element, not through the list view:
the two-argument call `(h 1 2)` does not select the three-argument equation and
gives the partial application `(partial h (1 2))`, as PeTTa does; `(h cons 1 2)`
gives `2`. -/
theorem cons_head_not_selected_by_shorter_call :
    answersOf (evaluate consHead 64 Effects.empty (call "h" [int 1, int 2])) =
      some [partialValue "h" [int 1, int 2]] ∧
    answersOf (evaluate consHead 64 Effects.empty (call "h" [sym "cons", int 1, int 2])) =
      some [int 2] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.BetaInliningControls
