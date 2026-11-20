import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Separation

/-!
# The typed refinement: code of a `T`

A parameter typed `(Code T)` receives its argument as written, and its type says what running the
text yields. At an occurrence, the type `E` the position expects decides:

* running fits when `T` fits `E` (`fitsRun`): `E` is on the computation line above `T`, or a type
  variable that may stand for `T`, or `%Undefined%`;
* passing fits when `(Code T)` fits `E` (`fitsPass`): `E` is `(Code T)`, `Atom`, `%Undefined%`, or a
  type variable that may stand for `(Code T)` (it must not occur in `T`).

`decision T E` is `run` or `pass` when exactly one fits, `needsDefault` when both do, `mismatch`
when neither does.

**The class needing a default** (`needsDefault_iff`): for a result type `T` that is `Number`,
`Bool`, `Proc` or a variable, a default is needed exactly at positions expecting `%Undefined%` or a
type variable that does not occur in `T`. `Number`, `Bool`, `Proc`, `Atom`, `(Code T)` and the
variable of `T` itself all decide.

**The typed elaboration** (`elabT`, into the same core) passes each position's expected type down:
the body's root expects the declared result, a `let` body inherits, a `let` source and a field of an
undeclared head expect `%Undefined%`, an argument expects its parameter's declared type, `+` expects
`Number`. A `(Code T)` variable runs when `decision T E` says so, and at the uninformative positions
when the default `dflt` says so. Plain `Atom` parameters stay data; values are final.

**The weakening law fixes the default** (`typed_default_fixed`): `Number` positions are
informative and run, `%Undefined%` positions need the default, so `dflt = pass` changes `5` into
`(f a)` when `Number` is weakened to `%Undefined%`, and only `dflt = run` keeps the answer.

**HE's `if` in this form** is `(: if (-> Bool (Code $t) (Code $t) $t))`. Its branch at the root
expects `$t`, the variable of its own code type, so running is decided without any default
(`typedIf_runs_branch`), and a call's two branches are checked against one `$t`
(`checkIfCall`): `(if True 1 True)` is rejected, while HE's `(-> Bool Atom Atom $t)` constrains
nothing and accepts it (`he_if_accepts_mixed_branches`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core Acceptance

namespace Typed

/-! ## Types and the decision -/

/-- Types of the typed refinement. -/
inductive CTy where
  | number
  | bool
  | proc
  | undef
  | atom
  | var (name : String)
  /-- Code whose run yields a value of the given type. -/
  | code (result : CTy)
  deriving DecidableEq, Repr

/-- The type variables of a type. -/
def CTy.vars : CTy → List String
  | .var a => [a]
  | .code t => t.vars
  | _ => []

/-- A parameter of this type receives its argument as written. -/
def CTy.holds : CTy → Bool
  | .atom => true
  | .code _ => true
  | _ => false

/-- The check a declared type makes on a value. -/
def CTy.check : CTy → Option Kind
  | .number => some .number
  | .bool => some .bool
  | _ => none

/-- The computation line: `Number` and `Bool` below `Proc` below `%Undefined%`. -/
def lineLE : CTy → CTy → Bool
  | .number, .number => true
  | .number, .proc => true
  | .bool, .bool => true
  | .bool, .proc => true
  | .proc, .proc => true
  | _, _ => false

/-- Running code of type `T` fits a position expecting `E`. -/
def fitsRun (T E : CTy) : Bool :=
  match E with
  | .undef => true
  | .var a => T == .var a || !(T.vars.contains a)
  | _ =>
      match T with
      | .var _ => E == .number || E == .bool || E == .proc
      | _ => lineLE T E

/-- Passing code of type `T` fits a position expecting `E`. -/
def fitsPass (T E : CTy) : Bool :=
  match E with
  | .undef => true
  | .atom => true
  | .code T' => T' == T
  | .var a => !(T.vars.contains a)
  | _ => false

/-- What an occurrence of a `(Code T)` variable does where `E` is expected. -/
inductive Decision where
  | run
  | pass
  | needsDefault
  | mismatch
  deriving DecidableEq, Repr

def decision (T E : CTy) : Decision :=
  match fitsRun T E, fitsPass T E with
  | true, false => .run
  | false, true => .pass
  | true, true => .needsDefault
  | false, false => .mismatch

/-- The types a run can yield here: `Number`, `Bool`, `Proc`, or a type variable. -/
def RunResult (T : CTy) : Prop := T = .number ∨ T = .bool ∨ T = .proc ∨ ∃ b, T = .var b

theorem decision_needsDefault (T E : CTy) :
    decision T E = .needsDefault ↔ fitsRun T E = true ∧ fitsPass T E = true := by
  unfold decision
  cases fitsRun T E <;> cases fitsPass T E <;> simp

/-- **The exact class of positions needing a default.** -/
theorem needsDefault_iff (T E : CTy) (hT : RunResult T) :
    decision T E = .needsDefault ↔ (E = .undef ∨ ∃ a, E = .var a ∧ T.vars.contains a = false) := by
  rw [decision_needsDefault]
  cases E with
  | undef => simp [fitsRun, fitsPass]
  | var a =>
      simp only [fitsRun, fitsPass]
      constructor
      · rintro ⟨_, h⟩
        exact .inr ⟨a, rfl, by simpa using h⟩
      · rintro (h | ⟨a', h, hc⟩)
        · cases h
        · cases h
          have hm : a ∉ T.vars := by simpa using hc
          simpa using ⟨Or.inr hm, hm⟩
  | atom => rcases hT with rfl | rfl | rfl | ⟨b, rfl⟩ <;> simp [fitsRun, fitsPass, lineLE]
  | number => rcases hT with rfl | rfl | rfl | ⟨b, rfl⟩ <;> simp [fitsRun, fitsPass, lineLE]
  | bool => rcases hT with rfl | rfl | rfl | ⟨b, rfl⟩ <;> simp [fitsRun, fitsPass, lineLE]
  | proc => rcases hT with rfl | rfl | rfl | ⟨b, rfl⟩ <;> simp [fitsRun, fitsPass, lineLE]
  | code T' => rcases hT with rfl | rfl | rfl | ⟨b, rfl⟩ <;> simp [fitsRun, fitsPass, lineLE]

/-- Positive and negative examples of the decision. -/
theorem decision_controls :
    decision .number .number = .run ∧ decision .number .proc = .run ∧
      decision .number (.code .number) = .pass ∧ decision .number .atom = .pass ∧
      decision .number .undef = .needsDefault ∧ decision .number (.var "s") = .needsDefault ∧
      decision (.var "t") (.var "t") = .run ∧ decision (.var "t") (.var "s") = .needsDefault ∧
      decision .number .bool = .mismatch ∧ decision .number (.code .bool) = .mismatch := by
  decide

/-! ## The typed elaboration -/

/-- A typed surface function. -/
structure TFn where
  head : String
  decl : Option (List CTy × CTy)
  eqns : List (List Atom × Atom)

/-- A typed surface program. -/
abbrev TProg := List TFn

def TFn.arity (fn : TFn) : Nat :=
  match fn.decl with
  | some (ps, _) => ps.length
  | none => (fn.eqns.head?.map fun e => e.1.length).getD 0

def TFn.params (fn : TFn) : List CTy :=
  match fn.decl with
  | some (ps, _) => ps
  | none => List.replicate fn.arity .undef

def TFn.result (fn : TFn) : CTy :=
  match fn.decl with
  | some (_, r) => r
  | none => .undef

/-- Parameter types of each head at each arity. -/
abbrev TModes := String → Nat → Option (List CTy)

def tmodesOf (P : TProg) : TModes := fun h n =>
  (P.find? fun fn => fn.head == h && fn.arity == n).map TFn.params

/-- Whether an occurrence runs: by the decision, and by the default where it is needed. -/
def decideAt (dflt : Bool) (T E : CTy) : Bool :=
  match decision T E with
  | .run => true
  | .pass => false
  | .needsDefault => dflt
  | .mismatch => false

/-- The held variables in scope, each with its code type (`none` for a plain `Atom`). -/
abbrev Held := List (String × Option CTy)

/-- The variables held parameters bind, with the code type of their parameter. -/
def heldTyped : List CTy → List Atom → Held
  | p :: ps, a :: as =>
      (match p with
        | .code T => (patVars a).map fun x => (x, some T)
        | .atom => (patVars a).map fun x => (x, none)
        | _ => []) ++ heldTyped ps as
  | _, _ => []

/-- An occurrence of a variable where `E` is expected. -/
def elabTVar (dflt : Bool) (held : Held) (E : CTy) (x : String) : Comp :=
  match held.lookup x with
  | some (some T) => if decideAt dflt T E then .run (.var x) else .ret (.var x)
  | _ => .ret (.var x)

mutual
/-- Elaborate a term at a position expecting `E`. -/
def elabT (dflt : Bool) (ms : TModes) (held : Held) (E : CTy) : Atom → Comp
  | .var x => elabTVar dflt held E x
  | .expression [.symbol "let", .var y, src, body] =>
      .bind (elabT dflt ms held .undef src) y
        (elabT dflt ms (held.filter fun p => p.1 != y) E body)
  | .expression [.symbol "+", a, b] =>
      .bind (elabT dflt ms held .number a) (slot 0)
        (.bind (elabT dflt ms held .number b) (slot 1) (.plus (.var (slot 0)) (.var (slot 1))))
  | .expression (.symbol h :: args) =>
      match ms h args.length with
      | some ps => elabTArgs dflt ms held ps args 0 [] (.call h)
      | none =>
          elabTArgs dflt ms held (List.replicate args.length .undef) args 0 []
            fun items => .ret (.expression (.symbol h :: items))
  | a => .ret a

/-- Arguments at their parameters' declared types; held ones as written. -/
def elabTArgs (dflt : Bool) (ms : TModes) (held : Held) :
    List CTy → List Atom → Nat → List Atom → (List Atom → Comp) → Comp
  | p :: ps, a :: as, i, acc, k =>
      if p.holds then elabTArgs dflt ms held ps as (i + 1) (acc ++ [a]) k
      else
        .bind (elabT dflt ms held p a) (slot i)
          (elabTArgs dflt ms held ps as (i + 1) (acc ++ [.var (slot i)]) k)
  | _, _, _, acc, k => k acc
end

/-- A typed function in the core: an `Atom` result returns its body as written. -/
def elabTFn (dflt : Bool) (ms : TModes) (fn : TFn) : Def where
  head := fn.head
  arity := fn.arity
  argChecks := fn.params.map CTy.check
  resultCheck := fn.result.check
  clauses := fn.eqns.map fun e =>
    (e.1, match fn.result with
      | .atom => .ret e.2
      | R => elabT dflt ms (heldTyped fn.params e.1) R e.2)

/-- A typed program; running a datum elaborates it where `%Undefined%` is expected. -/
def elabTProg (dflt : Bool) (P : TProg) : Prog where
  defs := P.map (elabTFn dflt (tmodesOf P))
  code := elabT dflt (tmodesOf P) [] .undef

/-- The printed answers of a query. -/
def tanswers (dflt : Bool) (P : TProg) (fuel : Nat) (q : Atom) : Option (List Atom) :=
  (exec (elabTProg dflt P) fuel (.comp [] (elabT dflt (tmodesOf P) [] .undef q))).map
    (observe true)

/-! ## The default, fixed by weakening -/

/-- `(= (f a) 5)`. -/
def tfA : TFn := ⟨"f", none, [([S "a"], N 5)]⟩

/-- `(: g (-> (Code Number) R)) (= (g $x) $x)`. -/
def codeId (R : CTy) : TProg := [tfA, ⟨"g", some ([.code .number], R), [([V "x"], V "x")]⟩]

/-- Under `Number` and `Proc` the occurrence is informative and runs; under `%Undefined%` and an
unrelated type variable the default decides. -/
theorem typed_body_rows :
    tanswers true (codeId .number) F qRange = some [N 5] ∧
    tanswers false (codeId .number) F qRange = some [N 5] ∧
    tanswers true (codeId .proc) F qRange = some [N 5] ∧
    tanswers false (codeId .proc) F qRange = some [N 5] ∧
    tanswers true (codeId .undef) F qRange = some [N 5] ∧
    tanswers false (codeId .undef) F qRange = some [callFA] ∧
    tanswers true (codeId (.var "s")) F qRange = some [N 5] ∧
    tanswers false (codeId (.var "s")) F qRange = some [callFA] ∧
    tanswers true (codeId .atom) F qRange = some [callFA] ∧
    tanswers false (codeId .atom) F qRange = some [callFA] := by
  decide +kernel

/-- A printed refusal. -/
def isErrorAtom : Atom → Bool
  | .expression (.symbol "Error" :: _) => true
  | _ => false

/-- The weakening law for the typed design on its result types (`Number` to `%Undefined%` here):
a run that printed no refusal keeps its answers. -/
def TypedWeakeningAt (dflt : Bool) (R R' : CTy) : Prop :=
  ∀ (L : List Atom), tanswers dflt (codeId R) F qRange = some L →
    L.all (fun a => !isErrorAtom a) = true → tanswers dflt (codeId R') F qRange = some L

/-- **The weakening law fixes the default**: with `dflt = pass` it fails from `Number` to
`%Undefined%`; with `dflt = run` the answers agree on the line. -/
theorem typed_default_fixed :
    ¬ TypedWeakeningAt false .number .undef ∧
      tanswers true (codeId .number) F qRange = tanswers true (codeId .proc) F qRange ∧
      tanswers true (codeId .proc) F qRange = tanswers true (codeId .undef) F qRange ∧
      tanswers true (codeId .undef) F qRange = tanswers true (codeId (.var "s")) F qRange := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro h
  have := h [N 5] (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

/-- Nested positions take their own expected types: a field of an undeclared head expects
`%Undefined%` (the default decides), an argument of `(: num-id (-> Number Number))` expects
`Number` (it runs under either default), and a `(Code Number)` argument passes the text. -/
def nestedTyped (body : Atom) (extra : List TFn) : TProg :=
  [tfA, ⟨"g", some ([.code .number], .undef), [([V "x"], body)]⟩] ++ extra

def numId : TFn := ⟨"num-id", some ([.number], .number), [([V "z"], V "z")]⟩

def codeArg : TFn := ⟨"code-arg", some ([.code .number], .atom), [([V "z"], V "z")]⟩

theorem typed_nested_rows :
    tanswers true (nestedTyped (E [S "wrap", V "x"]) []) F qRange =
      some [E [S "wrap", N 5]] ∧
    tanswers false (nestedTyped (E [S "wrap", V "x"]) []) F qRange =
      some [E [S "wrap", callFA]] ∧
    tanswers true (nestedTyped (E [S "num-id", V "x"]) [numId]) F qRange = some [N 5] ∧
    tanswers false (nestedTyped (E [S "num-id", V "x"]) [numId]) F qRange = some [N 5] ∧
    tanswers true (nestedTyped (E [S "code-arg", V "x"]) [codeArg]) F qRange = some [callFA] ∧
    tanswers false (nestedTyped (E [S "code-arg", V "x"]) [codeArg]) F qRange = some [callFA] := by
  decide +kernel

/-! ## HE's `if`, typed -/

/-- `(: if (-> Bool (Code $t) (Code $t) $t))` with HE's two equations. -/
def typedIf : TFn :=
  ⟨"tif", some ([.bool, .code (.var "t"), .code (.var "t")], .var "t"),
    [([S "True", V "then", V "else"], V "then"), ([S "False", V "then", V "else"], V "else")]⟩

/-- The branch at the root expects `$t`, the variable of its own code type: running is decided,
under either default. -/
theorem typedIf_runs_branch :
    decision (.var "t") (.var "t") = .run ∧
    tanswers true [tfA, typedIf] F (E [S "tif", S "True", callFA, E [S "boom"]]) = some [N 5] ∧
    tanswers false [tfA, typedIf] F (E [S "tif", S "True", callFA, E [S "boom"]]) = some [N 5] := by
  decide +kernel

/-- The type a term is known to have: a numeral is a `Number`, `True`/`False` a `Bool`, a call of a
declared head its declared result, anything else `%Undefined%`. -/
def typeOfTerm (ms : TProg) : Atom → CTy
  | .grounded (.int _) => .number
  | .symbol "True" => .bool
  | .symbol "False" => .bool
  | .expression (.symbol h :: args) =>
      match ms.find? (fun fn => fn.head == h && fn.arity == args.length) with
      | some fn => match fn.decl with
          | some (_, r) => r
          | none => .undef
      | none => .undef
  | _ => .undef

/-- Whether two known types can stand for one type variable (`%Undefined%` is consistent with
anything). -/
def agree : CTy → CTy → Bool
  | .undef, _ => true
  | _, .undef => true
  | a, b => a == b

/-- Check a call's arguments against the parameters: an evaluated parameter's argument must have a
compatible type; every `(Code $t)` argument's type must agree with every other one for `$t`. -/
def checkIfCall (ms : TProg) (params : List CTy) (args : List Atom) : Bool :=
  let pairs := params.zip args
  let codeTypes := pairs.filterMap fun pa =>
    match pa.1 with
    | .code (.var _) => some (typeOfTerm ms pa.2)
    | _ => none
  let evaluatedOk := pairs.all fun pa =>
    match pa.1 with
    | .bool => agree .bool (typeOfTerm ms pa.2)
    | .number => agree .number (typeOfTerm ms pa.2)
    | _ => true
  evaluatedOk && codeTypes.all fun a => codeTypes.all fun b => agree a b

/-- **Both branches are checked against one `$t`**: mixed branches are rejected, agreeing ones and
undeclared calls accepted; a non-Boolean condition is rejected. -/
theorem typedIf_checks_branches :
    checkIfCall [tfA, typedIf] [.bool, .code (.var "t"), .code (.var "t")]
        [S "True", N 1, S "True"] = false ∧
    checkIfCall [tfA, typedIf] [.bool, .code (.var "t"), .code (.var "t")]
        [S "True", N 1, N 2] = true ∧
    checkIfCall [tfA, typedIf] [.bool, .code (.var "t"), .code (.var "t")]
        [S "True", N 1, callFA] = true ∧
    checkIfCall [tfA, typedIf] [.bool, .code (.var "t"), .code (.var "t")]
        [N 5, N 1, N 2] = false := by
  decide

/-- HE's signature `(-> Bool Atom Atom $t)` constrains neither branch: the same mixed call is
accepted. -/
theorem he_if_accepts_mixed_branches :
    checkIfCall [tfA, typedIf] [.bool, .atom, .atom] [S "True", N 1, S "True"] = true := by
  decide

end Typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
