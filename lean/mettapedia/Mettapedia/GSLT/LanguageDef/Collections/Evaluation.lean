import Mettapedia.Logic.Unification.ListSpliceEncoding

/-!
# Where evaluation happens: data positions, result rules and list values

A big-step semantics over list-value terms (`Logic.Unification.ListSplice`)
that says exactly which positions are evaluated and which hold data. A term in
code position evaluates (`Eval`) in an environment of bound values to a value;
values are data.

**Positions that hold data, never evaluated.**
* A list literal, open or closed, with every element in it: it evaluates to
  its instance under the environment and to nothing else (`eval_list_iff`,
  `eval_rest_iff`).
* An argument passed to a data parameter, an `Atom` or `(Data T)` parameter:
  it arrives as written, instantiated (`receive_data_iff`).
* The argument of `quote` (`eval_quote_iff`).
* An element chosen by `superpose`, an atom stored in a space, and the two
  terms given to `unify`: they are matched or unified as data
  (`eval_superpose_iff`, `eval_match_iff`, `eval_unify_iff`).
* The output of a native that returns data, such as a conversion between
  lists and expressions (`eval_listFrom_iff`, `eval_tupleFrom_iff`).

**Positions that are evaluated.**
* An expression whose head is not a function: its elements, giving one result
  per combination of their values (`eval_construct_iff`).
* The arguments of evaluated parameters; the value of a `let`; the list given
  to `superpose` or `list:map`.
* A template once its pattern has matched: the body of `let`, the template of
  `match` and the chosen branch of `unify`, with the bindings read by the
  dialect's binding rule (`eval_let_iff`); and the body of `list:map`, which is
  instantiated with each element and run (`eval_map_iff`). `list:map` is the
  explicit way to evaluate the elements of a list.

**Three rules distinguish the dialects** (`Dialect`):
* the binding rule, `Lookup`: a bound variable in code position reads its
  value as data, or runs it (the binding is substituted into the code);
* the result rule, `Returning`, chosen by the declared result type: an
  equation's right-hand side is returned `asWritten`, or evaluated `once`, its
  value returned as data;
* the output rule, the same choice for the output of a native: kept as data,
  or run once as code (`Output`).

`Dialect.he` substitutes bindings into the code; the raw result of a call,
the right-hand side or a native's output, is returned as written when the
declared result type is `Atom` and is evaluated once otherwise. That single
evaluation of the substituted right-hand side is what HE's interpreter means
by evaluating a result again: it evaluates the reduct of the call, never the
reduct's value a second time (`HECorrespondence`). `Dialect.petta` reads
bindings as data, returns an `Atom` result as written, runs other bodies once
and keeps a native's output as data. `Dialect.primeCandidate`, a proposal,
reads bindings as data and runs every body once: an `Atom` or `(Data T)`
result is the body's value returned as data, and data held by an `Atom`
parameter stays data when it is substituted. A template that should not run
is written with `quote`.

**Conversions.** `list:from` takes its argument evaluated and returns the list
of the expression's elements as data; `tuple:from` returns the expression of a
list's elements as data. Where a native's output is kept as data, both are pure
data conversions (`eval_listFrom_iff`, `eval_tupleFrom_iff`), and a list
literal survives `tuple:from` then `list:from` unchanged (`eval_round_trip`). The controls
in `EvaluationControls` replay a probe table under the three dialects and show
that HE, which runs a native's output, runs the data `tuple:from` converted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.Evaluation

open Mettapedia.Logic.Unification.ListSplice

variable {Var : Type}

/-- The heads of the built-in operations. -/
inductive Builtin where
  | let_
  | unify
  | superpose
  | map
  | match_
  | quote
  deriving DecidableEq, Repr

/-- The leaves of terms: a built-in head or a symbol. -/
inductive Leaf (Symbol : Type) where
  | builtin (b : Builtin)
  | sym (a : Symbol)
  deriving DecidableEq, Repr

variable {Symbol : Type}

/-- Terms over symbols, with list values (`Logic.Unification.ListSplice`). -/
abbrev Tm (Symbol Var : Type) := Term (Leaf Symbol) Var

/-- An environment: the value of each variable, `Term.var x` when unbound. -/
abbrev Env (Symbol Var : Type) := Var → Tm Symbol Var

/-- A term instantiated by an environment, in splice normal form. -/
def inst (θ : Env Symbol Var) (t : Tm Symbol Var) : Tm Symbol Var := normalize (subst θ t)

/-- How a parameter receives its argument. -/
inductive Passing where
  /-- As written, instantiated by the environment: an `Atom` or `(Data T)` parameter. -/
  | data
  /-- Evaluated first. -/
  | evaluated
  deriving DecidableEq, Repr

/-- What happens to the raw result of a call: an equation's right-hand side,
or a native's output. -/
inductive Returning where
  /-- Returned as written, not evaluated. -/
  | asWritten
  /-- Evaluated once; its value is returned as data. -/
  | once
  deriving DecidableEq, Repr

/-- How a variable bound to a value reads in code position. -/
inductive Lookup where
  /-- Its value, as data. -/
  | data
  /-- Its value, evaluated as code: the binding is substituted into the code. -/
  | code
  deriving DecidableEq, Repr

/-- A program: the binding rule, the stored atoms and the functions. -/
structure Program (Symbol Var : Type) where
  /-- How bound variables read in code position. -/
  lookup : Lookup
  /-- The atoms of the space that `match` reads. -/
  stored : List (Tm Symbol Var)
  /-- How each function takes its arguments; `none` for symbols that are not functions. -/
  passing : Symbol → Option (List Passing)
  /-- Natives: received arguments and the value computed. -/
  native : Symbol → List (Tm Symbol Var) → Tm Symbol Var → Prop
  /-- Equations: received arguments, the environment binding the parameters,
  and the right-hand side. -/
  rule : Symbol → List (Tm Symbol Var) → Env Symbol Var → Tm Symbol Var → Prop
  /-- What happens to each equation's right-hand side. -/
  returning : Symbol → Returning
  /-- What happens to each native's output. -/
  nativeReturning : Symbol → Returning

namespace Program

variable (P : Program Symbol Var)

/-- An expression that is not a call: its head is neither a built-in head nor
a function. -/
def NotCall : List (Tm Symbol Var) → Prop
  | .atom (.builtin _) :: _ => False
  | .atom (.sym f) :: _ => P.passing f = none
  | _ => True

variable [DecidableEq Var]

/-- The environment after a pattern matched with `σ`: the pattern's variables
are bound to their values and shadow earlier bindings. -/
def bindPattern (θ : Env Symbol Var) (σ : Var → Tm Symbol Var) (p : Tm Symbol Var) :
    Env Symbol Var :=
  fun v => if v ∈ (Encoding.encode p).freeVars then normalize (σ v) else θ v

/-- The environment after unification with `σ`: its bindings apply to every value. -/
def afterUnify (θ : Env Symbol Var) (σ : Var → Tm Symbol Var) : Env Symbol Var :=
  fun v => inst σ (θ v)

/-- One more binding. -/
def bindOne (θ : Env Symbol Var) (x : Var) (value : Tm Symbol Var) : Env Symbol Var :=
  fun v => if v = x then value else θ v

end Program

variable [DecidableEq Symbol] [DecidableEq Var]

/-- A built-in head as a term. -/
abbrev head (b : Builtin) : Tm Symbol Var := .atom (.builtin b)

open Program in
mutual

/-- `Eval P θ t v`: the term `t`, in code position, evaluates to the value `v`. -/
inductive Eval (P : Program Symbol Var) : Env Symbol Var → Tm Symbol Var → Tm Symbol Var → Prop
  | symbol {θ a} : P.passing a = none → Eval P θ (.atom (.sym a)) (.atom (.sym a))
  | builtin {θ b} : Eval P θ (.atom (.builtin b)) (.atom (.builtin b))
  | variableData {θ x} : P.lookup = .data → Eval P θ (.var x) (θ x)
  | variableFree {θ x} : θ x = .var x → Eval P θ (.var x) (.var x)
  | variableCode {θ x v} : P.lookup = .code → θ x ≠ .var x → Eval P Term.var (θ x) v →
      Eval P θ (.var x) v
  | list {θ xs} : Eval P θ (.list xs) (inst θ (.list xs))
  | rest {θ xs tail} : Eval P θ (.rest xs tail) (inst θ (.rest xs tail))
  | construct {θ xs vs} : P.NotCall xs → EvalAll P θ xs vs → Eval P θ (.expr xs) (.expr vs)
  | native {θ f modes args received value result} :
      P.passing f = some modes → Receive P θ modes args received → P.native f received value →
      Output P (P.nativeReturning f) value result → Eval P θ (.expr (.atom (.sym f) :: args)) result
  | call {θ f modes args received σ rhs result} :
      P.passing f = some modes → Receive P θ modes args received → P.rule f received σ rhs →
      Return P (P.returning f) σ rhs result → Eval P θ (.expr (.atom (.sym f) :: args)) result
  | quote {θ t} : Eval P θ (.expr [head .quote, t]) (inst θ t)
  | letIn {θ p value bound σ body result} :
      Eval P θ value bound → Equivalent (subst σ p) bound →
      Eval P (bindPattern θ σ p) body result →
      Eval P θ (.expr [head .let_, p, value, body]) result
  | unifyYes {θ s t σ yes no result} :
      Encoding.solve (inst θ s) (inst θ t) = some σ → Eval P (afterUnify θ σ) yes result →
      Eval P θ (.expr [head .unify, s, t, yes, no]) result
  | unifyNo {θ s t yes no result} :
      Encoding.solve (inst θ s) (inst θ t) = none → Eval P θ no result →
      Eval P θ (.expr [head .unify, s, t, yes, no]) result
  | superpose {θ source xs element} :
      Eval P θ source (.list xs) → element ∈ xs →
      Eval P θ (.expr [head .superpose, source]) element
  | matchStored {θ p template atom σ result} :
      atom ∈ P.stored → Equivalent (subst σ p) atom →
      Eval P (bindPattern θ σ p) template result →
      Eval P θ (.expr [head .match_, p, template]) result
  | map {θ source x body xs ys} :
      Eval P θ source (.list xs) → EvalEach P θ x body xs ys →
      Eval P θ (.expr [head .map, source, .var x, body]) (.list ys)

/-- Each term of a list evaluates. -/
inductive EvalAll (P : Program Symbol Var) :
    Env Symbol Var → List (Tm Symbol Var) → List (Tm Symbol Var) → Prop
  | nil {θ} : EvalAll P θ [] []
  | cons {θ x xs v vs} : Eval P θ x v → EvalAll P θ xs vs → EvalAll P θ (x :: xs) (v :: vs)

/-- Arguments received by parameters. -/
inductive Receive (P : Program Symbol Var) :
    Env Symbol Var → List Passing → List (Tm Symbol Var) → List (Tm Symbol Var) → Prop
  | nil {θ} : Receive P θ [] [] []
  | data {θ modes x xs ys} : Receive P θ modes xs ys →
      Receive P θ (.data :: modes) (x :: xs) (inst θ x :: ys)
  | evaluated {θ modes x xs v ys} : Eval P θ x v → Receive P θ modes xs ys →
      Receive P θ (.evaluated :: modes) (x :: xs) (v :: ys)

/-- A right-hand side and the result of the call. -/
inductive Return (P : Program Symbol Var) :
    Returning → Env Symbol Var → Tm Symbol Var → Tm Symbol Var → Prop
  | asWritten {σ rhs} : Return P .asWritten σ rhs (inst σ rhs)
  | once {σ rhs v} : Eval P σ rhs v → Return P .once σ rhs v

/-- A native's output and the result of the call: kept as data, or run once as
code. -/
inductive Output (P : Program Symbol Var) : Returning → Tm Symbol Var → Tm Symbol Var → Prop
  | asWritten {value} : Output P .asWritten value value
  | once {value result} : Eval P Term.var value result → Output P .once value result

/-- The body of `list:map` is a template: for each element it is instantiated
with the element and the instance is evaluated as code. -/
inductive EvalEach (P : Program Symbol Var) :
    Env Symbol Var → Var → Tm Symbol Var → List (Tm Symbol Var) → List (Tm Symbol Var) → Prop
  | nil {θ x body} : EvalEach P θ x body [] []
  | cons {θ x body e es y ys} : Eval P Term.var (inst (bindOne θ x e) body) y →
      EvalEach P θ x body es ys → EvalEach P θ x body (e :: es) (y :: ys)

end

variable {P : Program Symbol Var} {θ : Env Symbol Var}

/-! ## Data positions -/

/-- **A list literal is data**: it evaluates to its instance and to nothing else. -/
theorem eval_list_iff (xs : List (Tm Symbol Var)) (v : Tm Symbol Var) :
    Eval P θ (.list xs) v ↔ v = inst θ (.list xs) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .list

/-- An open or improper literal is data too. -/
theorem eval_rest_iff (xs : List (Tm Symbol Var)) (tail v : Tm Symbol Var) :
    Eval P θ (.rest xs tail) v ↔ v = inst θ (.rest xs tail) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .rest

/-- Under the data rule a bound variable reads its value as data. -/
theorem eval_var_iff (data : P.lookup = .data) (x : Var) (v : Tm Symbol Var) :
    Eval P θ (.var x) v ↔ v = θ x := by
  constructor
  · intro h
    cases h with
    | variableData => rfl
    | variableFree free => exact free.symm ▸ rfl
    | variableCode code => rw [data] at code; cases code
  · rintro rfl; exact .variableData data

/-- Under the code rule a bound variable runs its value. -/
theorem eval_var_code_iff (code : P.lookup = .code) (x : Var) (bound : θ x ≠ .var x)
    (v : Tm Symbol Var) : Eval P θ (.var x) v ↔ Eval P Term.var (θ x) v := by
  constructor
  · intro h
    cases h with
    | variableData data => rw [code] at data; cases data
    | variableFree free => exact absurd free bound
    | variableCode _ _ run => exact run
  · exact .variableCode code bound

/-- A symbol that is not a function is a value. -/
theorem eval_sym_iff (a : Symbol) (v : Tm Symbol Var) :
    Eval P θ (.atom (.sym a)) v ↔ P.passing a = none ∧ v = .atom (.sym a) := by
  constructor
  · intro h; cases h with | symbol none_ => exact ⟨none_, rfl⟩
  · rintro ⟨none_, rfl⟩; exact .symbol none_

/-- `quote` returns its argument as written, instantiated: an explicit template. -/
theorem eval_quote_iff (t v : Tm Symbol Var) :
    Eval P θ (.expr [head .quote, t]) v ↔ v = inst θ t := by
  constructor
  · intro h
    cases h with
    | quote => rfl
    | construct notCall _ => exact notCall.elim
  · rintro rfl; exact .quote

/-- A data parameter receives its argument as written. -/
theorem receive_data_iff (x : Tm Symbol Var) (ys : List (Tm Symbol Var)) :
    Receive P θ [.data] [x] ys ↔ ys = [inst θ x] := by
  constructor
  · intro h
    cases h with
    | data rest => cases rest; rfl
  · rintro rfl; exact .data .nil

/-- An evaluated parameter receives a value of its argument. -/
theorem receive_evaluated_iff (x : Tm Symbol Var) (ys : List (Tm Symbol Var)) :
    Receive P θ [.evaluated] [x] ys ↔ ∃ v, Eval P θ x v ∧ ys = [v] := by
  constructor
  · intro h
    cases h with
    | evaluated value rest => cases rest; exact ⟨_, value, rfl⟩
  · rintro ⟨v, value, rfl⟩; exact .evaluated value .nil

theorem return_asWritten_iff (σ : Env Symbol Var) (rhs r : Tm Symbol Var) :
    Return P .asWritten σ rhs r ↔ r = inst σ rhs := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .asWritten

theorem return_once_iff (σ : Env Symbol Var) (rhs r : Tm Symbol Var) :
    Return P .once σ rhs r ↔ Eval P σ rhs r := by
  constructor
  · intro h; cases h with | once value => exact value
  · exact .once

theorem output_asWritten_iff (value result : Tm Symbol Var) :
    Output P .asWritten value result ↔ result = value := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .asWritten

theorem output_once_iff (value result : Tm Symbol Var) :
    Output P .once value result ↔ Eval P Term.var value result := by
  constructor
  · intro h; cases h with | once run => exact run
  · exact .once

/-- **An element chosen by `superpose` is data**: one result per element of the
evaluated list, never evaluated itself. -/
theorem eval_superpose_iff (source v : Tm Symbol Var) :
    Eval P θ (.expr [head .superpose, source]) v ↔ ∃ xs, Eval P θ source (.list xs) ∧ v ∈ xs := by
  constructor
  · intro h
    cases h with
    | superpose listed member => exact ⟨_, listed, member⟩
    | construct notCall _ => exact notCall.elim
  · rintro ⟨xs, listed, member⟩
    exact .superpose listed member

/-- **Stored atoms are data**: `match` binds its pattern against a stored atom
and evaluates only the template. -/
theorem eval_match_iff (p template v : Tm Symbol Var) :
    Eval P θ (.expr [head .match_, p, template]) v ↔
      ∃ atom ∈ P.stored, ∃ σ, Equivalent (subst σ p) atom ∧
        Eval P (Program.bindPattern θ σ p) template v := by
  constructor
  · intro h
    cases h with
    | matchStored stored matched evaluated => exact ⟨_, stored, _, matched, evaluated⟩
    | construct notCall _ => exact notCall.elim
  · rintro ⟨atom, stored, σ, matched, evaluated⟩
    exact .matchStored stored matched evaluated

/-- `let` evaluates its value, binds its pattern as data, and evaluates its body. -/
theorem eval_let_iff (p value body v : Tm Symbol Var) :
    Eval P θ (.expr [head .let_, p, value, body]) v ↔
      ∃ bound σ, Eval P θ value bound ∧ Equivalent (subst σ p) bound ∧
        Eval P (Program.bindPattern θ σ p) body v := by
  constructor
  · intro h
    cases h with
    | letIn evaluated matched body => exact ⟨_, _, evaluated, matched, body⟩
    | construct notCall _ => exact notCall.elim
  · rintro ⟨bound, σ, evaluated, matched, body⟩
    exact .letIn evaluated matched body

/-- `unify` unifies its two terms as data and evaluates the chosen branch. -/
theorem eval_unify_iff (s t yes no v : Tm Symbol Var) :
    Eval P θ (.expr [head .unify, s, t, yes, no]) v ↔
      (∃ σ, Encoding.solve (inst θ s) (inst θ t) = some σ ∧
          Eval P (Program.afterUnify θ σ) yes v) ∨
        (Encoding.solve (inst θ s) (inst θ t) = none ∧ Eval P θ no v) := by
  constructor
  · intro h
    cases h with
    | unifyYes solved branch => exact Or.inl ⟨_, solved, branch⟩
    | unifyNo failed branch => exact Or.inr ⟨failed, branch⟩
    | construct notCall _ => exact notCall.elim
  · rintro (⟨σ, solved, branch⟩ | ⟨failed, branch⟩)
    · exact .unifyYes solved branch
    · exact .unifyNo failed branch

/-- `list:map` instantiates its body with each element, evaluates each
instance, and collects the values in order. -/
theorem eval_map_iff (source body : Tm Symbol Var) (x : Var) (v : Tm Symbol Var) :
    Eval P θ (.expr [head .map, source, .var x, body]) v ↔
      ∃ xs ys, Eval P θ source (.list xs) ∧ EvalEach P θ x body xs ys ∧ v = .list ys := by
  constructor
  · intro h
    cases h with
    | map listed each => exact ⟨_, _, listed, each, rfl⟩
    | construct notCall _ => exact notCall.elim
  · rintro ⟨xs, ys, listed, each, rfl⟩
    exact .map listed each

/-- An expression that is not a call evaluates element by element: one result
per combination of the elements' values. -/
theorem eval_construct_iff (xs : List (Tm Symbol Var)) (notCall : P.NotCall xs)
    (v : Tm Symbol Var) :
    Eval P θ (.expr xs) v ↔ ∃ vs, EvalAll P θ xs vs ∧ v = .expr vs := by
  constructor
  · intro h
    cases h with
    | construct _ each => exact ⟨_, each, rfl⟩
    | native passing => simp [Program.NotCall, passing] at notCall
    | call passing => simp [Program.NotCall, passing] at notCall
    | quote => exact notCall.elim
    | letIn => exact notCall.elim
    | unifyYes => exact notCall.elim
    | unifyNo => exact notCall.elim
    | superpose => exact notCall.elim
    | matchStored => exact notCall.elim
    | map => exact notCall.elim
  · rintro ⟨vs, each, rfl⟩
    exact .construct notCall each

/-- A call of a function: its received arguments and its result rule. -/
theorem eval_call_iff (f : Symbol) (args : List (Tm Symbol Var)) (v : Tm Symbol Var) :
    Eval P θ (.expr (.atom (.sym f) :: args)) v ↔
      (P.passing f = none ∧ ∃ vs, EvalAll P θ (.atom (.sym f) :: args) vs ∧ v = .expr vs) ∨
        ∃ modes received, P.passing f = some modes ∧ Receive P θ modes args received ∧
          ((∃ value, P.native f received value ∧ Output P (P.nativeReturning f) value v) ∨
            ∃ σ rhs, P.rule f received σ rhs ∧ Return P (P.returning f) σ rhs v) := by
  constructor
  · intro h
    cases h with
    | construct notCall each => exact Or.inl ⟨notCall, _, each, rfl⟩
    | native passing received computed output =>
        exact Or.inr ⟨_, _, passing, received, Or.inl ⟨_, computed, output⟩⟩
    | call passing received rule returned =>
        exact Or.inr ⟨_, _, passing, received, Or.inr ⟨_, _, rule, returned⟩⟩
  · rintro (⟨notCall, vs, each, rfl⟩ |
        ⟨modes, received, passing, receives, ⟨value, computed, output⟩ | ⟨σ, rhs, rule, returned⟩⟩)
    · exact .construct notCall each
    · exact .native passing receives computed output
    · exact .call passing receives rule returned

/-! ## Dialects: the result rule as a function of the declared result type -/

/-- The declared result type of a function, defined by equations or native. -/
inductive ResultType where
  /-- `Atom`, or `(Data T)`. -/
  | data
  /-- `%Undefined%`, or any other type. -/
  | undefined
  deriving DecidableEq, Repr

/-- A dialect's binding rule, result rule and output rule. -/
structure Dialect where
  lookup : Lookup
  returning : ResultType → Returning
  /-- What becomes of a native's output, by the native's declared result type. -/
  nativeReturning : ResultType → Returning

/-- HE: bindings are substituted into the code. The raw result of a call, an
equation's right-hand side or a native's output, is returned as written at
`Atom` and evaluated once at any other type. Data held by an `Atom` parameter
therefore runs once it lands in code position or in a result. -/
def Dialect.he : Dialect :=
  ⟨.code, fun | .data => .asWritten | .undefined => .once,
    fun | .data => .asWritten | .undefined => .once⟩

/-- PeTTa: bindings read as data; an `Atom` result is the body as written;
otherwise the body runs once and its result is not evaluated again. A native's
output is data. -/
def Dialect.petta : Dialect :=
  ⟨.data, fun | .data => .asWritten | .undefined => .once, fun _ => .asWritten⟩

/-- The candidate rule for Prime, a proposal: bindings read as data, the body
always runs once, and no result is evaluated again. Data held by an `Atom`
parameter therefore stays data, and a template that should not run is
written with `quote`. A native's output is data. -/
def Dialect.primeCandidate : Dialect := ⟨.data, fun _ => .once, fun _ => .asWritten⟩

/-! ## Conversions between lists and expressions -/

/-- The native that reads an expression's elements as a list, its output data. -/
def ListFrom (P : Program Symbol Var) (f : Symbol) : Prop :=
  P.passing f = some [.evaluated] ∧
    (∀ received value, P.native f received value ↔ ∃ xs, received = [.expr xs] ∧ value = .list xs) ∧
    (∀ received σ rhs, ¬ P.rule f received σ rhs) ∧ P.nativeReturning f = .asWritten

/-- The native that reads a list's elements as an expression, its output
data. -/
def TupleFrom (P : Program Symbol Var) (f : Symbol) : Prop :=
  P.passing f = some [.evaluated] ∧
    (∀ received value, P.native f received value ↔ ∃ xs, received = [.list xs] ∧ value = .expr xs) ∧
    (∀ received σ rhs, ¬ P.rule f received σ rhs) ∧ P.nativeReturning f = .asWritten

/-- **`list:from` is a data conversion of an evaluated argument.** -/
theorem eval_listFrom_iff {f : Symbol} (native : ListFrom P f) (argument v : Tm Symbol Var) :
    Eval P θ (.expr [.atom (.sym f), argument]) v ↔
      ∃ xs, Eval P θ argument (.expr xs) ∧ v = .list xs := by
  rw [eval_call_iff]
  constructor
  · rintro (⟨notFunction, -⟩ |
        ⟨modes, received, passing, receives, ⟨output, computed, delivered⟩ | ⟨σ, rhs, rule, -⟩⟩)
    · rw [native.1] at notFunction; cases notFunction
    · rw [native.1] at passing
      cases passing
      rw [native.2.2.2, output_asWritten_iff] at delivered
      subst delivered
      obtain ⟨w, value, rfl⟩ := (receive_evaluated_iff argument _).mp receives
      obtain ⟨xs, same, rfl⟩ := (native.2.1 _ _).mp computed
      cases same
      exact ⟨xs, value, rfl⟩
    · exact absurd rule (native.2.2.1 _ _ _)
  · rintro ⟨xs, value, rfl⟩
    exact Or.inr ⟨_, _, native.1, .evaluated value .nil,
      Or.inl ⟨_, (native.2.1 _ _).mpr ⟨xs, rfl, rfl⟩, by rw [native.2.2.2]; exact .asWritten⟩⟩

/-- **`tuple:from` is a data conversion**: a list's elements, as an expression
that is not evaluated again. -/
theorem eval_tupleFrom_iff {f : Symbol} (native : TupleFrom P f) (argument v : Tm Symbol Var) :
    Eval P θ (.expr [.atom (.sym f), argument]) v ↔
      ∃ xs, Eval P θ argument (.list xs) ∧ v = .expr xs := by
  rw [eval_call_iff]
  constructor
  · rintro (⟨notFunction, -⟩ |
        ⟨modes, received, passing, receives, ⟨output, computed, delivered⟩ | ⟨σ, rhs, rule, -⟩⟩)
    · rw [native.1] at notFunction; cases notFunction
    · rw [native.1] at passing
      cases passing
      rw [native.2.2.2, output_asWritten_iff] at delivered
      subst delivered
      obtain ⟨w, value, rfl⟩ := (receive_evaluated_iff argument _).mp receives
      obtain ⟨xs, same, rfl⟩ := (native.2.1 _ _).mp computed
      cases same
      exact ⟨xs, value, rfl⟩
    · exact absurd rule (native.2.2.1 _ _ _)
  · rintro ⟨xs, value, rfl⟩
    exact Or.inr ⟨_, _, native.1, .evaluated value .nil,
      Or.inl ⟨_, (native.2.1 _ _).mpr ⟨xs, rfl, rfl⟩, by rw [native.2.2.2]; exact .asWritten⟩⟩

omit [DecidableEq Symbol] [DecidableEq Var] in
/-- A literal's instance is again a list value. -/
theorem inst_list (xs : List (Tm Symbol Var)) :
    inst θ (.list xs) = .list (xs.map (inst θ)) := by
  simp [inst, normalize, subst, List.map_map, Function.comp_def]

/-- **A list literal survives both conversions unchanged**, its elements
unevaluated: `list:from (tuple:from L) = L` as data. -/
theorem eval_round_trip {listHead tupleHead : Symbol} (listNative : ListFrom P listHead)
    (tupleNative : TupleFrom P tupleHead) (xs : List (Tm Symbol Var)) (v : Tm Symbol Var) :
    Eval P θ (.expr [.atom (.sym listHead), .expr [.atom (.sym tupleHead), .list xs]]) v ↔
      v = inst θ (.list xs) := by
  rw [eval_listFrom_iff listNative]
  constructor
  · rintro ⟨ys, inner, rfl⟩
    obtain ⟨zs, literal, same⟩ := (eval_tupleFrom_iff tupleNative _ _).mp inner
    cases same
    rw [eval_list_iff, inst_list] at literal
    cases literal
    rw [inst_list]
  · intro value
    refine ⟨xs.map (inst θ), (eval_tupleFrom_iff tupleNative _ _).mpr
      ⟨xs.map (inst θ), (eval_list_iff _ _).mpr (inst_list xs).symm, rfl⟩, ?_⟩
    rw [value, inst_list]

end Mettapedia.GSLT.LanguageDef.Collections.Evaluation
