import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Nested

/-!
# The type of a position decides whether text runs

One elaboration into the study's core (`Core`), for declared programs over `Typed.CTy`.

**Positions and their types.** Every position of a term has an expected type, computed from the
declarations alone: the root of a body expects the declared result; an argument expects its
parameter's declared type; a `let` source, the argument of `eval` and a field of a head without a
declaration expect `%Undefined%`; the arguments of `+` expect `Number`. There is no new surface
form: the surface is the study's (`let`, `eval`, `+` special), with `(Code T)` among the types. To
hold text at a value position a program calls a function whose parameter and result hold, such as
`(: hold (-> Atom Atom)) (= (hold $a) $a)` (the idiom measured on all three systems).

**Modes.** A type *holds* when it is `Atom` or `(Code T)` (`CTy.holds`); every other type is a
value type. The rule:

* at a position whose type holds, the term is returned as written (instantiated);
* at a position of a value type, the term is evaluated: a held variable there runs its text
  (`.run`), a value variable is final (`.ret`).

**The family** (`TDesign`, two choices). The study's typed refinement had one default for the
positions where both readings fit; here the family has two choices, so that each law can be shown
to force its choice:

* `dflt`: at an *ambiguous* value position (`%Undefined%`, or a type variable that does not occur in
  the code's own type), held text runs;
* `atomRuns`: plain `Atom` text runs at value positions (otherwise only `(Code T)` text does, and
  `Atom` text stays data everywhere).

`byType` is `⟨true, true⟩`: held text runs at every value position and is quoted at every held
position; the type of the position is the only thing consulted (`runsAt_byType`).

**How the elaboration is written.** `elabW` takes the decision as data: `rd E x` says whether held
variable `x` runs at a position of type `E`, and `r` is the decision at the current position. The
elaborator consults the declarations only through `modeView`, in which every held parameter type
reads as `Atom` (only its mode is ever used). A design is a choice of `rd` (`rdOf`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core Typed

namespace ByType

/-! ## The family -/

/-- A typed design: two choices (see the module text). -/
structure TDesign where
  /-- At an ambiguous value position, held text runs. -/
  dflt : Bool
  /-- Plain `Atom` text runs at value positions. -/
  atomRuns : Bool
  deriving DecidableEq, Repr

/-- The position's type decides: held text runs at every value position. -/
def byType : TDesign := ⟨true, true⟩

/-- Only `(Code T)` text runs; plain `Atom` text is data; the default at ambiguous positions runs. -/
def codeOnly : TDesign := ⟨true, false⟩

/-- `Atom` text runs where the position is informative; ambiguous positions pass. -/
def atomPass : TDesign := ⟨false, true⟩

/-- The study's typed refinement with the default "pass": `Atom` is data, ambiguous positions pass. -/
def typedPass : TDesign := ⟨false, false⟩

/-- A value position is ambiguous for held text of kind `k` (`none` for `Atom`, `some T` for
`(Code T)`) when its type is `%Undefined%` or a type variable that does not occur in `T`. -/
def ambiguous (k : Option CTy) (E : CTy) : Bool :=
  match E with
  | .undef => true
  | .var a =>
      match k with
      | some T => !(T.vars.contains a)
      | none => true
  | _ => false

/-- Whether held text of kind `k` runs at a position expecting `E`. -/
def runsAt (td : TDesign) (k : Option CTy) (E : CTy) : Bool :=
  !E.holds && (k.isSome || td.atomRuns) && (!ambiguous k E || td.dflt)

/-- In `byType` only the position's mode counts. -/
theorem runsAt_byType (k : Option CTy) (E : CTy) : runsAt byType k E = !E.holds := by
  simp [runsAt, byType]

/-- Where the default runs, which value type a position has does not matter. -/
theorem runsAt_dflt (td : TDesign) (hd : td.dflt = true) (k : Option CTy) {E : CTy}
    (hE : E.holds = false) : runsAt td k E = (k.isSome || td.atomRuns) := by
  simp [runsAt, hd, hE]

/-- At a held position nothing runs. -/
theorem runsAt_held (td : TDesign) (k : Option CTy) {E : CTy} (hE : E.holds = true) :
    runsAt td k E = false := by
  simp [runsAt, hE]

/-! ## What the elaborator sees of declarations -/

/-- A held type read as `Atom`; value types unchanged. -/
def eraseTy : CTy → CTy
  | .code _ => .atom
  | T => T

theorem eraseTy_holds (T : CTy) : (eraseTy T).holds = T.holds := by
  cases T <;> rfl

theorem eraseTy_check (T : CTy) : (eraseTy T).check = T.check := by
  cases T <;> rfl

theorem eraseTy_value {T : CTy} (h : T.holds = false) : eraseTy T = T := by
  cases T <;> simp_all [CTy.holds, eraseTy]

theorem eraseTy_eraseTy (T : CTy) : eraseTy (eraseTy T) = eraseTy T := by
  cases T <;> rfl

/-- What the elaborator sees of the declarations: each head's parameter types, every held one read
as `Atom`. -/
def modeView (ms : TModes) : TModes := fun h n => (ms h n).map (List.map eraseTy)

/-! ## The elaboration -/

/-- The variables that held parameters bind. -/
def heldNames : List CTy → List Atom → List String
  | p :: ps, a :: as => (if p.holds then patVars a else []) ++ heldNames ps as
  | _, _ => []

/-- The kind of a held variable: `some T` for `(Code T)`, `none` for `Atom` (and for a name not
listed). -/
def kindOf (kinds : Held) (x : String) : Option CTy := (kinds.lookup x).getD none

/-- A design's decision: does held variable `x` run at a position of type `E`. -/
def rdOf (td : TDesign) (kinds : Held) : CTy → String → Bool :=
  fun E x => runsAt td (kindOf kinds x) E

mutual
/-- Elaborate a term at a value position. `held` lists the held variables in scope; `r x` says
whether `x` runs here; `rd E` gives that decision at a position of type `E`. Held positions never
reach this function: they quote. -/
def elabW (ms : TModes) (rd : CTy → String → Bool) (held : List String) (r : String → Bool) :
    Atom → Comp
  | .var x => if held.contains x && r x then .run (.var x) else .ret (.var x)
  | .expression [.symbol "let", .var y, src, body] =>
      .bind (elabW ms rd held (rd .undef) src) y (elabW ms rd (held.erase y) r body)
  | .expression [.symbol "eval", m] =>
      .bind (elabW ms rd held (rd .undef) m) "#e" (.run (.var "#e"))
  | .expression [.symbol "+", a, b] =>
      .bind (elabW ms rd held (rd .number) a) (slot 0)
        (.bind (elabW ms rd held (rd .number) b) (slot 1)
          (.plus (.var (slot 0)) (.var (slot 1))))
  | .expression (.symbol h :: args) =>
      match ms h args.length with
      | some ps => elabArgsW ms rd held ps args 0 [] (.call h)
      | none =>
          elabArgsW ms rd held (List.replicate args.length .undef) args 0 []
            fun items => .ret (.expression (.symbol h :: items))
  | a => .ret a

/-- Arguments at their parameters' types: at a held parameter the argument is passed as written,
at a value parameter it is evaluated and its value passed. -/
def elabArgsW (ms : TModes) (rd : CTy → String → Bool) (held : List String) :
    List CTy → List Atom → Nat → List Atom → (List Atom → Comp) → Comp
  | p :: ps, a :: as, i, acc, k =>
      if p.holds then elabArgsW ms rd held ps as (i + 1) (acc ++ [a]) k
      else
        .bind (elabW ms rd held (rd p) a) (slot i)
          (elabArgsW ms rd held ps as (i + 1) (acc ++ [.var (slot i)]) k)
  | _, _, _, acc, k => k acc
end

/-- A design's elaboration at a value position of type `E`. -/
def elabV (td : TDesign) (ms : TModes) (kinds : Held) (held : List String) (E : CTy) (t : Atom) :
    Comp :=
  elabW (modeView ms) (rdOf td kinds) held (rdOf td kinds E) t

/-- A body under its declared result: quoted under a held result, evaluated under a value
result. -/
def bodyB (td : TDesign) (ms : TModes) (kinds : Held) (held : List String) (R : CTy)
    (body : Atom) : Comp :=
  if R.holds then .ret body else elabV td ms kinds held R body

/-- A function's definition in the core. -/
def elabFnB (td : TDesign) (ms : TModes) (fn : TFn) : Def where
  head := fn.head
  arity := fn.arity
  argChecks := fn.params.map CTy.check
  resultCheck := fn.result.check
  clauses := fn.eqns.map fun e =>
    (e.1, bodyB td ms (heldTyped fn.params e.1) (heldNames fn.params e.1) fn.result e.2)

/-- A query: a term at a position expecting `%Undefined%`, with nothing held. -/
def queryB (td : TDesign) (P : TProg) (q : Atom) : Comp :=
  elabV td (tmodesOf P) [] [] .undef q

/-- A whole program; running a datum elaborates it as a query. -/
def elabProgB (td : TDesign) (P : TProg) : Prog where
  defs := P.map (elabFnB td (tmodesOf P))
  code := queryB td P

/-- A query's run at a fuel. -/
def runB (td : TDesign) (P : TProg) (n : Nat) (q : Atom) : Option (List Ans) :=
  exec (elabProgB td P) n (.comp [] (queryB td P q))

/-- The printed answers (a refusal prints as an error atom). -/
def answersB (td : TDesign) (P : TProg) (n : Nat) (q : Atom) : Option (List Atom) :=
  (runB td P n q).map (observe true)

/-- The query prints `L` with some fuel. -/
def PrintsB (td : TDesign) (P : TProg) (q : Atom) (L : List Atom) : Prop :=
  ∃ n, answersB td P n q = some L

/-! ## Which positions run, decided from the declarations alone -/

/-- The decision of `byType`: run exactly at value positions, whatever the variable's kind. -/
theorem rdOf_byType (kinds : Held) : rdOf byType kinds = fun E _ => !E.holds := by
  funext E x
  simp [rdOf, runsAt_byType]

/-- A held result quotes the whole body. -/
theorem bodyB_held (td : TDesign) (ms : TModes) (kinds : Held) (held : List String) {R : CTy}
    (hR : R.holds = true) (body : Atom) : bodyB td ms kinds held R body = .ret body := by
  simp [bodyB, hR]

/-- A value result evaluates the body. -/
theorem bodyB_value (td : TDesign) (ms : TModes) (kinds : Held) (held : List String) {R : CTy}
    (hR : R.holds = false) (body : Atom) :
    bodyB td ms kinds held R body = elabV td ms kinds held R body := by
  simp [bodyB, hR]

/-- A held parameter receives its argument as written. -/
theorem elabArgsW_held (ms : TModes) (rd : CTy → String → Bool) (held : List String)
    {p : CTy} (hp : p.holds = true) (ps : List CTy) (a : Atom) (as : List Atom) (i : Nat)
    (acc : List Atom) (k : List Atom → Comp) :
    elabArgsW ms rd held (p :: ps) (a :: as) i acc k =
      elabArgsW ms rd held ps as (i + 1) (acc ++ [a]) k := by
  rw [elabArgsW]; simp [hp]

/-- A value parameter receives the value of its argument, evaluated with its own decision. -/
theorem elabArgsW_value (ms : TModes) (rd : CTy → String → Bool) (held : List String)
    {p : CTy} (hp : p.holds = false) (ps : List CTy) (a : Atom) (as : List Atom) (i : Nat)
    (acc : List Atom) (k : List Atom → Comp) :
    elabArgsW ms rd held (p :: ps) (a :: as) i acc k =
      .bind (elabW ms rd held (rd p) a) (slot i)
        (elabArgsW ms rd held ps as (i + 1) (acc ++ [.var (slot i)]) k) := by
  rw [elabArgsW]; simp [hp]

/-- **In `byType` a held variable runs exactly at value positions**; a variable that is not held
is final. -/
theorem elabV_var_byType (ms : TModes) (kinds : Held) (held : List String) (E : CTy)
    (x : String) :
    elabV byType ms kinds held E (.var x) =
      if held.contains x && !E.holds then .run (.var x) else .ret (.var x) := by
  simp [elabV, elabW, rdOf_byType]

/-- Running held text is running it as a query: the text bound to the variable, elaborated where
`%Undefined%` is expected, with nothing held. -/
theorem exec_run_text (td : TDesign) (P : TProg) (n : Nat) (ρ : Env) (x : String) :
    exec (elabProgB td P) (n + 1) (.comp ρ (.run (.var x))) =
      exec (elabProgB td P) n (.comp [] (queryB td P (inst ρ (.var x)))) := rfl

/-! ## Controls, run by the kernel -/

open Acceptance

/-- `(: g (-> H R)) (= (g $x) $x)`. -/
def heldIdT (g : String) (H R : CTy) : TFn := ⟨g, some ([H], R), [([V "x"], V "x")]⟩

/-- `(: g (-> H R)) (= (g $x) B)`. -/
def heldBodyT (g : String) (H R : CTy) (B : Atom) : TFn := ⟨g, some ([H], R), [([V "x"], B)]⟩

/-- The held identity on `(f a)` in `byType`: it runs under every value result and is quoted
under every held result, whether the parameter is `Atom` or `(Code Number)`. -/
theorem byType_positions :
    answersB byType [tfA, heldIdT "g" .atom .number] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" .atom .proc] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" .atom .undef] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" .atom (.var "t")] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" .atom .atom] F qRange = some [callFA] ∧
    answersB byType [tfA, heldIdT "g" .atom (.code .number)] F qRange = some [callFA] ∧
    answersB byType [tfA, heldIdT "g" (.code .number) .number] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" (.code .number) .undef] F qRange = some [N 5] ∧
    answersB byType [tfA, heldIdT "g" (.code .number) (.code .number)] F qRange =
      some [callFA] := by
  decide +kernel

/-- `(: hold (-> Atom Atom)) (= (hold $a) $a)`. -/
def holdFn : TFn := ⟨"hold", some ([.atom], .atom), [([V "a"], V "a")]⟩

/-- The explicit hold: `(hold $x)` at a value position gives the text as a value, which is final;
inside a field each occurrence follows its own position. -/
theorem byType_hold :
    answersB byType [tfA, holdFn, heldBodyT "g" .atom .undef (E [S "hold", V "x"])] F qRange =
      some [callFA] ∧
    answersB byType
        [tfA, holdFn, heldBodyT "g" .atom .undef (E [S "wrap", E [S "hold", V "x"], V "x"])]
        F qRange = some [E [S "wrap", callFA, N 5]] := by
  decide +kernel

/-- The other three designs on the same held identity: `codeOnly` and `typedPass` keep plain
`Atom` text as data (under `Number` the check then refuses it); the two designs with `dflt = false`
pass `(Code Number)` text at `%Undefined%`. -/
theorem family_positions :
    answersB codeOnly [tfA, heldIdT "g" .atom .undef] F qRange = some [callFA] ∧
    answersB codeOnly [tfA, heldIdT "g" (.code .number) .undef] F qRange = some [N 5] ∧
    answersB typedPass [tfA, heldIdT "g" (.code .number) .number] F qRange = some [N 5] ∧
    answersB typedPass [tfA, heldIdT "g" (.code .number) .undef] F qRange = some [callFA] ∧
    answersB atomPass [tfA, heldIdT "g" .atom .proc] F qRange = some [N 5] ∧
    answersB atomPass [tfA, heldIdT "g" .atom .undef] F qRange = some [callFA] ∧
    answersB codeOnly [tfA, heldIdT "g" .atom .number] F qRange =
      some [E [S "Error", callFA, E [S "BadType", S "Number"]]] := by
  decide +kernel

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
