import Batteries.Data.List.Perm
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Ring
import Mettapedia.Machines.RegisteredArity

/-!
# Which declarations govern a typed PeTTa call

A PeTTa name may have equations at several arities and declarations
`(: f (-> A₁ … Aₘ R))` of several input counts.  An application of `f` to `n`
arguments is a call, a partial application, an over-application or data, by the
arities of its equations (`RegisteredArity.reference`).  This module compares
the rules that decide which declarations govern such an application, and how
many alternatives it gets.

* **Delivery** (`deliver`): an input typed `Atom` receives its argument as
  written; any other input receives its value, with the writes evaluating it
  makes; a checked input that refuses its value stops the delivery, keeping the
  writes made so far.
* **Rules** (`Rule`): `exact` (a call is governed by the declarations of its own
  input count, a partial application by the longer ones); `atLeast` (every
  declaration with at least as many inputs as arguments, whatever the
  application: SWI-PeTTa's written calls since its declaration-count filter);
  `exactElseLonger` (the exact declarations if there are any, else the longer
  ones); `declaredArityIsCall` (a declaration of `n` inputs makes an `n`-ary
  application a call even without an equation of that arity; a partial
  application takes every declaration with at least `n` inputs: CeTTa's PeTTa
  lane at the time of writing).
* **Alternatives**: a call gets one alternative per distinct governing
  declaration; a partial application gets one per distinct declaration
  (`perDeclaration`) or one per distinct list of types at its supplied positions
  (`perPlan`).
* **Routes**: `throughVariable` applies a name to some arguments, binds the
  answer, and applies it to the rest, as `(let $p (f a…) ($p b…))` does.

The laws, with the rule each one decides:

* `exact_locality`: under `exact`, a declaration changes only the calls of its
  own input count and the partial applications of fewer arguments.  Refuted for
  `atLeast` (`Controls.atLeast_not_local`) and `exactElseLonger`
  (`Controls.exactElseLonger_not_local`).
* `monotone_in_declarations`: under `exact` and `atLeast`, once an application
  is typed, adding a declaration only adds alternatives.  Refuted for
  `exactElseLonger` (`Controls.exactElseLonger_not_monotone`) and for
  `declaredArityIsCall` (`Controls.declaredArityIsCall_not_monotone`).
* `apply_congr_members`: every rule reads only which declarations are present,
  not their order or their copies (answers as a bag, writes equal).
* `no_rule_local_typing_partials_and_uniform`: no rule types a partial
  application by the longer declarations, keeps every declaration to calls of
  its own input count, and gives a longer declaration the same reach over a
  shorter call whether or not an equation of the shorter arity exists.  `exact`
  has the first two (`exact_typesPartials`, `exact_localOnCalls`); `atLeast` the
  first and the third (`atLeast_typesPartials`, `atLeast_sameReach`), and on every
  route it multiplies a completed partial application
  (`Controls.atLeast_every_route_multiplies`).
* `rules_agree_on_one_arity`: when a name's declarations and equations all have
  one arity, all four rules give every application the same run.  The weaker
  hypothesis (declarations of one arity, equations at others) does not suffice
  (`Controls.one_declared_arity_disagrees`).
* `exactPerPlan_completion`: under the exactPerPlan semantics (`exact`, `perPlan`), a
  partial application completed through a variable answers as the complete call
  does, when the longer declarations agree on the supplied positions, with the
  same writes when the completed arity has one distinct declaration or the
  supplied arguments write nothing.  Without the agreement the answers differ
  (`Controls.disagreeing_plans_complete_differently`); without one declaration
  or pure arguments the writes differ (`Controls.partial_writes_once`), and no
  partial step that evaluates before it knows the completion's arity can match
  both completions (`partial_writes_cannot_match_both`).

Stable-fixed's head selects complete calls by exact arity since #311 (2026-11-07) and runs a
typed body once per tuple of argument values since #313 (2026-11-08). The `c3adb86`
definitions below record the earlier behaviour these controls were measured on, not the
current reference, and `exactPerPlan` is a candidate studied here, not the head's rule.

The controls reproduce the answers measured on SWI-PeTTa stable-fixed `c3adb86`
and on CeTTa's PeTTa lane (Opt and main, both equation routes) on
2026-11-19.  The model has first-order arguments, one value per argument, and
no errors other than over-application.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeclarationArity

open Mettapedia.Machines.RegisteredArity (Kind reference)

/-! ## Values, types, arguments -/

/-- A first-order value: a number, a symbol, a truth value, or an argument held
as written. -/
inductive Item
  | num (n : ℕ)
  | sym (s : ℕ)
  | truth (b : Bool)
  | src (e : ℕ)
  deriving DecidableEq, Repr

/-- An answer: a first-order value, an application kept as data, a partial
application, or the over-application error of a name. -/
inductive Val
  | item (i : Item)
  | data (f : ℕ) (args : List Item)
  | partialApp (f : ℕ) (args : List Item)
  | overapplied (f : ℕ)
  deriving DecidableEq, Repr

/-- A type in a declaration, as the call protocol reads it: `Atom` holds its
argument as written and checks nothing, `%Undefined%` (or `_`) evaluates it and
checks nothing, and the other types evaluate it and check it. -/
inductive Ty
  | atom
  | undef
  | number
  | symbol
  | bool
  deriving DecidableEq, Repr

/-- Whether a value passes a type's check. -/
def admits : Ty → Item → Bool
  | .atom, _ => true
  | .undef, _ => true
  | .number, .num _ => true
  | .symbol, .sym _ => true
  | .bool, .truth _ => true
  | _, _ => false

/-- Whether an answer passes a result type's check: a value that is not
first-order, a partial application included, passes only `Atom` and
`%Undefined%`. -/
def admitsVal (t : Ty) : Val → Bool
  | .item i => admits t i
  | _ => decide (t = .atom) || decide (t = .undef)

/-- An argument as written: its source, its value, and the writes evaluating it
makes. -/
structure Arg where
  source : Item
  value : Item
  writes : ℕ
  deriving DecidableEq, Repr

/-- A value passed on as an argument: the same held or evaluated, with no
writes (a value is not run again). -/
def Arg.ofItem (i : Item) : Arg := ⟨i, i, 0⟩

/-- What an input of type `t` receives from an argument: the argument as written
for `Atom`, its value for any other type. -/
def pick (t : Ty) (a : Arg) : Item := if t = .atom then a.source else a.value

/-- The writes an input of type `t` makes of its argument: none for `Atom`, the
writes of evaluating it for any other type. -/
def cost (t : Ty) (a : Arg) : ℕ := if t = .atom then 0 else a.writes

@[simp] theorem pick_ofItem (t : Ty) (i : Item) : pick t (Arg.ofItem i) = i := by
  unfold pick Arg.ofItem; split <;> rfl

@[simp] theorem cost_ofItem (t : Ty) (i : Item) : cost t (Arg.ofItem i) = 0 := by
  unfold cost Arg.ofItem; split <;> rfl

theorem cost_pure (t : Ty) (a : Arg) (h : a.writes = 0) : cost t a = 0 := by
  unfold cost; split <;> simp [h]

/-- Deliver arguments by input types, left to right.  An `Atom` input receives
its argument as written; any other input receives its value and the writes of
evaluating it.  A checked input that refuses its value stops the delivery: no
values, and the writes made so far.  Arguments beyond the inputs are evaluated
unchecked; inputs beyond the arguments are not read. -/
def deliver : List Ty → List Arg → Option (List Item) × ℕ
  | [], as => (some (as.map Arg.value), (as.map Arg.writes).sum)
  | _ :: _, [] => (some [], 0)
  | t :: ts, a :: as =>
      if admits t (pick t a) then
        ((deliver ts as).1.map (pick t a :: ·), cost t a + (deliver ts as).2)
      else (none, cost t a)

theorem deliver_nil_left (as : List Arg) :
    deliver [] as = (some (as.map Arg.value), (as.map Arg.writes).sum) := by
  cases as <;> rfl

theorem deliver_cons (t : Ty) (ts : List Ty) (a : Arg) (as : List Arg) :
    deliver (t :: ts) (a :: as) =
      if admits t (pick t a) then
        ((deliver ts as).1.map (pick t a :: ·), cost t a + (deliver ts as).2)
      else (none, cost t a) := rfl

/-! ## Programs -/

/-- A declaration `(: name (-> inputs… result))`. -/
structure Decl where
  name : ℕ
  inputs : List Ty
  result : Ty
  deriving DecidableEq, Repr

/-- The number of inputs of a declaration. -/
def Decl.arity (d : Decl) : ℕ := d.inputs.length

/-- An equation of a name at an arity: its answers and its writes, for the
delivered values. -/
structure Eqn where
  name : ℕ
  arity : ℕ
  body : List Item → List Val × ℕ

/-- A program: its equations and its declarations. -/
structure Program where
  eqns : List Eqn
  decls : List Decl

/-- What an application gives: its answers, as a bag, and the writes it made. -/
abbrev Run := List Val × ℕ

/-- The runs of several alternatives together. -/
def Run.sum : List Run → Run
  | [] => ([], 0)
  | r :: rs => (r.1 ++ (Run.sum rs).1, r.2 + (Run.sum rs).2)

/-- The arities of a name's equations. -/
def arities (E : List Eqn) (f : ℕ) : List ℕ :=
  (E.filter fun e => decide (e.name = f)).map Eqn.arity

/-- P-APP-1's reading of an application to `n` arguments: a name with equations
is registered at their arities, a name without is data. -/
def kind (E : List Eqn) (f n : ℕ) : Kind :=
  reference (!(arities E f).isEmpty) (arities E f) n

/-- Every equation of a name at the number of delivered values, each answering
in turn. -/
def runEqns (E : List Eqn) (f : ℕ) (vs : List Item) : Run :=
  Run.sum ((E.filter fun e => decide (e.name = f ∧ e.arity = vs.length)).map
    fun e => e.body vs)

/-- A name's declarations. -/
def declsOf (D : List Decl) (f : ℕ) : List Decl := D.filter fun d => decide (d.name = f)

/-! ## Alternatives -/

/-- One typed alternative of a call: deliver by the declaration's inputs, run
the equations of the call's arity, and check each answer against the
declaration's result type. -/
def typedCall (E : List Eqn) (f : ℕ) (d : Decl) (args : List Arg) : Run :=
  match deliver d.inputs args with
  | (some vs, w) => ((runEqns E f vs).1.filter (admitsVal d.result), w + (runEqns E f vs).2)
  | (none, w) => ([], w)

/-- A call no declaration governs: every argument evaluated, nothing checked. -/
def untypedCall (E : List Eqn) (f : ℕ) (args : List Arg) : Run :=
  ((runEqns E f (args.map Arg.value)).1,
    (args.map Arg.writes).sum + (runEqns E f (args.map Arg.value)).2)

/-- One typed alternative of a partial application, delivered by `inputs`.
With `check`, the partial value must also pass the declaration's result type,
as the reference checks it today. -/
def typedPartial (f : ℕ) (inputs : List Ty) (result : Ty) (check : Bool)
    (args : List Arg) : Run :=
  match deliver inputs args with
  | (some vs, w) =>
      ((if !check || admitsVal result (.partialApp f vs) then [.partialApp f vs] else []), w)
  | (none, w) => ([], w)

/-! ## Rules -/

/-- Which declarations govern an application. -/
inductive Rule
  /-- A call: the declarations of its own input count.  A partial application:
  the longer declarations. -/
  | exact
  /-- Every declaration with at least as many inputs as arguments. -/
  | atLeast
  /-- A call: the declarations of its own input count if there are any, else
  the longer ones.  A partial application: the longer declarations. -/
  | exactElseLonger
  /-- A declaration of `n` inputs makes an `n`-ary application of a name with
  equations a call; a call takes the declarations of its own input count, a
  partial application every declaration with at least as many inputs. -/
  | declaredArityIsCall
  deriving DecidableEq, Repr

/-- How many alternatives a partial application gets. -/
inductive PartialAlternatives
  /-- One per distinct governing declaration. -/
  | perDeclaration
  /-- One per distinct list of types at the supplied positions. -/
  | perPlan
  deriving DecidableEq, Repr

/-- A semantics of typed applications. -/
structure Semantics where
  rule : Rule
  partials : PartialAlternatives
  /-- Whether a partial value is checked against its declaration's result type. -/
  checkPartialResult : Bool
  deriving DecidableEq, Repr

/-- How a rule reads an application: P-APP-1, except that under
`declaredArityIsCall` a declaration of the application's input count makes it a
call when the name has equations. -/
def appKind (R : Rule) (P : Program) (f n : ℕ) : Kind :=
  match R with
  | .declaredArityIsCall =>
      if !(arities P.eqns f).isEmpty && (declsOf P.decls f).any (fun d => decide (d.arity = n))
      then .call else kind P.eqns f n
  | _ => kind P.eqns f n

/-- The declarations a rule lets govern an application of a kind to `n`
arguments. -/
def eligible (R : Rule) (k : Kind) (n : ℕ) (ds : List Decl) : List Decl :=
  match R, k with
  | .exact, .call => ds.filter fun d => decide (d.arity = n)
  | .exact, _ => ds.filter fun d => decide (n < d.arity)
  | .atLeast, _ => ds.filter fun d => decide (n ≤ d.arity)
  | .exactElseLonger, .call =>
      if (ds.filter fun d => decide (d.arity = n)) = [] then ds.filter fun d => decide (n < d.arity)
      else ds.filter fun d => decide (d.arity = n)
  | .exactElseLonger, _ => ds.filter fun d => decide (n < d.arity)
  | .declaredArityIsCall, .call => ds.filter fun d => decide (d.arity = n)
  | .declaredArityIsCall, _ => ds.filter fun d => decide (n ≤ d.arity)

/-- The run of an application of `f` to `args`. -/
def apply (S : Semantics) (P : Program) (f : ℕ) (args : List Arg) : Run :=
  match appKind S.rule P f args.length with
  | .data => ([.data f (args.map Arg.value)], (args.map Arg.writes).sum)
  | .overapplied => ([.overapplied f], 0)
  | .call =>
      if (eligible S.rule .call args.length (declsOf P.decls f)).dedup = [] then
        untypedCall P.eqns f args
      else Run.sum ((eligible S.rule .call args.length (declsOf P.decls f)).dedup.map
        fun d => typedCall P.eqns f d args)
  | .partialApp =>
      if eligible S.rule .partialApp args.length (declsOf P.decls f) = [] then
        ([.partialApp f (args.map Arg.value)], (args.map Arg.writes).sum)
      else match S.partials with
        | .perDeclaration =>
            Run.sum ((eligible S.rule .partialApp args.length (declsOf P.decls f)).dedup.map
              fun d => typedPartial f d.inputs d.result S.checkPartialResult args)
        | .perPlan =>
            Run.sum (((eligible S.rule .partialApp args.length (declsOf P.decls f)).map
              fun d => d.inputs.take args.length).dedup.map
                fun p => typedPartial f p .undef false args)

/-! ## Routes -/

/-- A value applied to more arguments: a partial application's function applied
to its held values and then the new arguments; any other value is returned. -/
def complete (S : Semantics) (P : Program) (v : Val) (more : List Arg) : Run :=
  match v with
  | .partialApp g vs => apply S P g (vs.map Arg.ofItem ++ more)
  | v => ([v], 0)

/-- `(let $p (f as…) ($p bs…))`: each answer of the first application applied
to the rest, with the writes of both steps. -/
def throughVariable (S : Semantics) (P : Program) (f : ℕ) (as bs : List Arg) : Run :=
  ((Run.sum ((apply S P f as).1.map fun v => complete S P v bs)).1,
    (apply S P f as).2 + (Run.sum ((apply S P f as).1.map fun v => complete S P v bs)).2)

/-- SWI-PeTTa stable-fixed `c3adb86`, written calls: every declaration with at
least as many inputs as arguments, one alternative per declaration, a partial
value checked against the declaration's result type. -/
def c3adb86Written : Semantics := ⟨.atLeast, .perDeclaration, true⟩

/-- SWI-PeTTa's run-time dispatch (`reduce`, a head held by a variable): the
call is made without the declarations. -/
def c3adb86Dynamic (P : Program) (f : ℕ) (args : List Arg) : Run :=
  apply c3adb86Written ⟨P.eqns, []⟩ f args

/-- `(let $p (f as…) ($p bs…))` on SWI-PeTTa: the first application written, its
completion dispatched at run time. -/
def c3adb86ThroughVariable (P : Program) (f : ℕ) (as bs : List Arg) : Run :=
  ((Run.sum ((apply c3adb86Written P f as).1.map fun v =>
      match v with
      | .partialApp g vs => c3adb86Dynamic P g (vs.map Arg.ofItem ++ bs)
      | v => ([v], 0))).1,
    (apply c3adb86Written P f as).2 + (Run.sum ((apply c3adb86Written P f as).1.map fun v =>
      match v with
      | .partialApp g vs => c3adb86Dynamic P g (vs.map Arg.ofItem ++ bs)
      | v => ([v], 0))).2)

/-- CeTTa's PeTTa lane on 2026-11-19, on every route. -/
def cettaToday : Semantics := ⟨.declaredArityIsCall, .perDeclaration, false⟩

/-- The exactPerPlan semantics: a call is governed by the declarations of its own
input count, a partial application by the longer ones, with one alternative per
distinct list of types at its supplied positions; a partial value is checked
when it is completed, not before. -/
def exactPerPlan : Semantics := ⟨.exact, .perPlan, false⟩

/-! ## Laws -/

theorem declsOf_cons (D : List Decl) (d : Decl) (f : ℕ) :
    declsOf (d :: D) f = if d.name = f then d :: declsOf D f else declsOf D f := by
  unfold declsOf
  by_cases h : d.name = f <;> simp [h]

/-- Under `exact`, a declaration that is not of a call's own input count, and not
longer than a partial application, changes nothing the application gives. -/
theorem exact_locality (pa : PartialAlternatives) (c : Bool) (E : List Eqn) (D : List Decl)
    (f : ℕ) (d : Decl) (args : List Arg)
    (hcall : kind E f args.length = .call → d.arity ≠ args.length)
    (hpart : kind E f args.length = .partialApp → d.arity ≤ args.length) :
    apply ⟨.exact, pa, c⟩ ⟨E, d :: D⟩ f args = apply ⟨.exact, pa, c⟩ ⟨E, D⟩ f args := by
  have hc : kind E f args.length = .call →
      eligible .exact .call args.length (declsOf (d :: D) f) =
        eligible .exact .call args.length (declsOf D f) := by
    intro hk
    rw [declsOf_cons]
    split_ifs
    · simp [eligible, hcall hk]
    · rfl
  have hp : kind E f args.length = .partialApp →
      eligible .exact .partialApp args.length (declsOf (d :: D) f) =
        eligible .exact .partialApp args.length (declsOf D f) := by
    intro hk
    rw [declsOf_cons]
    split_ifs
    · have : ¬ args.length < d.arity := by have := hpart hk; omega
      simp [eligible, this]
    · rfl
  unfold apply
  simp only [appKind]
  cases hk : kind E f args.length with
  | data => rfl
  | overapplied => rfl
  | call => simp only [hc hk]
  | partialApp => simp only [hp hk]

/-- A rule types partial applications by the longer declarations. -/
def TypesPartials (el : Kind → ℕ → List Decl → List Decl) : Prop :=
  ∀ n ds d, d ∈ ds → n < d.arity → d ∈ el .partialApp n ds

/-- A rule keeps every declaration to the calls of its own input count. -/
def LocalOnCalls (el : Kind → ℕ → List Decl → List Decl) : Prop :=
  ∀ n ds d, d ∈ el .call n ds → d.arity = n

/-- A rule gives a longer declaration the same reach over a shorter application,
call or partial: whether an equation of the shorter arity exists does not
matter. -/
def SameReachOverShorter (el : Kind → ℕ → List Decl → List Decl) : Prop :=
  ∀ n ds d, n < d.arity → (d ∈ el .call n ds ↔ d ∈ el .partialApp n ds)

/-- **No rule has all three.**  A rule that types partial applications by the
longer declarations and keeps declarations to calls of their own input count
gives a longer declaration a reach over a shorter application that depends on
whether an equation of the shorter arity exists. -/
theorem no_rule_local_typing_partials_and_uniform (el : Kind → ℕ → List Decl → List Decl)
    (htypes : TypesPartials el) (hlocal : LocalOnCalls el) (huniform : SameReachOverShorter el) :
    False := by
  let d : Decl := ⟨0, [.atom], .atom⟩
  have hp : d ∈ el .partialApp 0 [d] := htypes 0 [d] d (by simp) (by decide)
  have hcall : d ∈ el .call 0 [d] := (huniform 0 [d] d (by decide)).mpr hp
  have := hlocal 0 [d] d hcall
  simp [d, Decl.arity] at this

theorem exact_typesPartials : TypesPartials (eligible .exact) := by
  intro n ds d hd hlt
  simp [eligible, hd, hlt]

theorem exact_localOnCalls : LocalOnCalls (eligible .exact) := by
  intro n ds d hd
  simp [eligible] at hd
  exact hd.2

theorem atLeast_typesPartials : TypesPartials (eligible .atLeast) := by
  intro n ds d hd hlt
  simp [eligible, hd, le_of_lt hlt]

theorem atLeast_sameReach : SameReachOverShorter (eligible .atLeast) := by
  intro n ds d _
  simp [eligible]

/-- Adding an element to a list adds at most one distinct element, whose run
comes first. -/
theorem sum_map_dedup_cons {α : Type} [DecidableEq α] (k : α → Run) (a : α) (l : List α) :
    List.Subperm (Run.sum (l.dedup.map k)).1 (Run.sum ((a :: l).dedup.map k)).1 ∧
    (Run.sum (l.dedup.map k)).2 ≤ (Run.sum ((a :: l).dedup.map k)).2 := by
  by_cases h : a ∈ l
  · rw [List.dedup_cons_of_mem h]
    exact ⟨List.Subperm.refl _, le_rfl⟩
  · rw [List.dedup_cons_of_notMem h]
    simp only [List.map_cons, Run.sum]
    exact ⟨(List.sublist_append_right _ _).subperm, Nat.le_add_left _ _⟩

/-- Under `exact` and `atLeast`, a declaration added to a name either joins the
governing declarations of an application, first, or leaves them as they were. -/
theorem eligible_declsOf_cons (R : Rule) (hR : R = .exact ∨ R = .atLeast) (k : Kind) (n : ℕ)
    (d : Decl) (D : List Decl) (f : ℕ) :
    eligible R k n (declsOf (d :: D) f) = eligible R k n (declsOf D f) ∨
      eligible R k n (declsOf (d :: D) f) = d :: eligible R k n (declsOf D f) := by
  rw [declsOf_cons]
  split_ifs
  · rcases hR with rfl | rfl <;> cases k <;> simp only [eligible, List.filter_cons] <;>
      split_ifs <;> simp
  · exact Or.inl rfl

/-- **Adding a declaration only adds alternatives** (`exact`, `atLeast`): once an
application is typed, the answers it had remain among its answers, and its
writes do not decrease. -/
theorem monotone_in_declarations (R : Rule) (hR : R = .exact ∨ R = .atLeast) (pa : PartialAlternatives)
    (c : Bool) (E : List Eqn) (D : List Decl) (f : ℕ) (d : Decl) (args : List Arg)
    (htyped : eligible R (kind E f args.length) args.length (declsOf D f) ≠ []) :
    List.Subperm (apply ⟨R, pa, c⟩ ⟨E, D⟩ f args).1 (apply ⟨R, pa, c⟩ ⟨E, d :: D⟩ f args).1 ∧
    (apply ⟨R, pa, c⟩ ⟨E, D⟩ f args).2 ≤ (apply ⟨R, pa, c⟩ ⟨E, d :: D⟩ f args).2 := by
  have hk : ∀ P : Program, appKind R P f args.length = kind P.eqns f args.length := by
    intro P; rcases hR with rfl | rfl <;> rfl
  unfold apply
  simp only [hk]
  cases hkind : kind E f args.length with
  | data => exact ⟨List.Subperm.refl _, le_rfl⟩
  | overapplied => exact ⟨List.Subperm.refl _, le_rfl⟩
  | call =>
      rw [hkind] at htyped
      have hne : (eligible R .call args.length (declsOf D f)).dedup ≠ [] := by
        rwa [Ne, List.dedup_eq_nil]
      rcases eligible_declsOf_cons R hR .call args.length d D f with h | h
      · simp only [h]; exact ⟨List.Subperm.refl _, le_rfl⟩
      · have hne' : (d :: eligible R .call args.length (declsOf D f)).dedup ≠ [] := by
          rw [Ne, List.dedup_eq_nil]; simp
        rw [h, if_neg hne, if_neg hne']
        exact sum_map_dedup_cons _ _ _
  | partialApp =>
      rw [hkind] at htyped
      rcases eligible_declsOf_cons R hR .partialApp args.length d D f with h | h
      · simp only [h]; exact ⟨List.Subperm.refl _, le_rfl⟩
      · simp only [if_neg htyped, h, List.cons_ne_nil, if_false]
        cases pa with
        | perDeclaration => exact sum_map_dedup_cons _ _ _
        | perPlan => simp only [List.map_cons]; exact sum_map_dedup_cons _ _ _

/-- Two lists with the same members, whatever their order and copies. -/
def SameMembers {α : Type} (l₁ l₂ : List α) : Prop := ∀ x, x ∈ l₁ ↔ x ∈ l₂

theorem SameMembers.filter {α : Type} {l₁ l₂ : List α} (h : SameMembers l₁ l₂) (p : α → Bool) :
    SameMembers (l₁.filter p) (l₂.filter p) := by
  intro x; simp [List.mem_filter, h x]

theorem SameMembers.map {α β : Type} {l₁ l₂ : List α} (h : SameMembers l₁ l₂) (g : α → β) :
    SameMembers (l₁.map g) (l₂.map g) := by
  intro x; simp [List.mem_map, h _]

theorem SameMembers.eq_nil_iff {α : Type} {l₁ l₂ : List α} (h : SameMembers l₁ l₂) :
    l₁ = [] ↔ l₂ = [] := by
  simp only [List.eq_nil_iff_forall_not_mem, h _]

theorem SameMembers.dedup_perm {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h : SameMembers l₁ l₂) : List.Perm l₁.dedup l₂.dedup :=
  (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).mpr
    fun a => by simp [List.mem_dedup, h a]

/-- Alternatives in another order give the same answers, as a bag, and the same
writes. -/
theorem sum_perm {α : Type} (k : α → Run) {l₁ l₂ : List α} (h : List.Perm l₁ l₂) :
    List.Perm (Run.sum (l₁.map k)).1 (Run.sum (l₂.map k)).1 ∧
      (Run.sum (l₁.map k)).2 = (Run.sum (l₂.map k)).2 := by
  induction h with
  | nil => exact ⟨List.Perm.refl _, rfl⟩
  | cons x _ ih =>
      simp only [List.map_cons, Run.sum]
      exact ⟨ih.1.append_left _, by rw [ih.2]⟩
  | swap x y l =>
      simp only [List.map_cons, Run.sum]
      refine ⟨?_, by omega⟩
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩

theorem declsOf_sameMembers {D₁ D₂ : List Decl} (h : SameMembers D₁ D₂) (f : ℕ) :
    SameMembers (declsOf D₁ f) (declsOf D₂ f) := h.filter _

theorem eligible_sameMembers (R : Rule) (k : Kind) (n : ℕ) {ds₁ ds₂ : List Decl}
    (h : SameMembers ds₁ ds₂) : SameMembers (eligible R k n ds₁) (eligible R k n ds₂) := by
  cases R <;> cases k <;> simp only [eligible] <;> try exact h.filter _
  all_goals
    have he := (h.filter fun d => decide (d.arity = n)).eq_nil_iff
    split_ifs with h₁ h₂ h₂
    · exact h.filter _
    · exact absurd (he.mp h₁) h₂
    · exact absurd (he.mpr h₂) h₁
    · exact h.filter _

theorem appKind_sameMembers (R : Rule) (E : List Eqn) {D₁ D₂ : List Decl}
    (h : SameMembers D₁ D₂) (f n : ℕ) : appKind R ⟨E, D₁⟩ f n = appKind R ⟨E, D₂⟩ f n := by
  cases R <;> simp only [appKind]
  have hany : (declsOf D₁ f).any (fun d => decide (d.arity = n)) =
      (declsOf D₂ f).any (fun d => decide (d.arity = n)) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (declsOf_sameMembers h f x).mp hx, hp⟩,
      fun ⟨x, hx, hp⟩ => ⟨x, (declsOf_sameMembers h f x).mpr hx, hp⟩⟩
  rw [hany]

/-- **Order and copies of declarations do not matter**, under every rule: two
programs whose declarations have the same members give every application the
same answers, as a bag, and the same writes. -/
theorem apply_congr_members (S : Semantics) (E : List Eqn) (D₁ D₂ : List Decl) (f : ℕ)
    (args : List Arg) (h : ∀ d, d ∈ D₁ ↔ d ∈ D₂) :
    List.Perm (apply S ⟨E, D₁⟩ f args).1 (apply S ⟨E, D₂⟩ f args).1 ∧
      (apply S ⟨E, D₁⟩ f args).2 = (apply S ⟨E, D₂⟩ f args).2 := by
  obtain ⟨R, pa, c⟩ := S
  have hk := appKind_sameMembers R E h f args.length
  have hd := declsOf_sameMembers h f
  unfold apply
  simp only [hk]
  cases appKind R ⟨E, D₂⟩ f args.length with
  | data => exact ⟨List.Perm.refl _, rfl⟩
  | overapplied => exact ⟨List.Perm.refl _, rfl⟩
  | call =>
      have hm := eligible_sameMembers R .call args.length hd
      have hnil : (eligible R .call args.length (declsOf D₁ f)).dedup = [] ↔
          (eligible R .call args.length (declsOf D₂ f)).dedup = [] := by
        simp only [List.dedup_eq_nil]; exact hm.eq_nil_iff
      by_cases h₂ : (eligible R .call args.length (declsOf D₂ f)).dedup = []
      · rw [if_pos (hnil.mpr h₂), if_pos h₂]; exact ⟨List.Perm.refl _, rfl⟩
      · rw [if_neg (mt hnil.mp h₂), if_neg h₂]; exact sum_perm _ hm.dedup_perm
  | partialApp =>
      have hm := eligible_sameMembers R .partialApp args.length hd
      by_cases h₂ : eligible R .partialApp args.length (declsOf D₂ f) = []
      · rw [if_pos (hm.eq_nil_iff.mpr h₂), if_pos h₂]; exact ⟨List.Perm.refl _, rfl⟩
      · rw [if_neg (mt hm.eq_nil_iff.mp h₂), if_neg h₂]
        cases pa with
        | perDeclaration => exact sum_perm _ hm.dedup_perm
        | perPlan => exact sum_perm _ (hm.map _).dedup_perm

/-- A name whose equations all have arity `m`: P-APP-1 reads `m` arguments as a
call, fewer as a partial application, more as an over-application. -/
theorem kind_one_arity (E : List Eqn) (f m n : ℕ) (he : ∀ e ∈ E, e.name = f → e.arity = m)
    (hex : ∃ e ∈ E, e.name = f) :
    kind E f n = if n = m then .call else if n < m then .partialApp else .overapplied := by
  have hmem : ∀ a, a ∈ arities E f ↔ a = m := by
    intro a
    simp only [arities, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨e, ⟨he₁, he₂⟩, rfl⟩; exact he e he₁ he₂
    · rintro rfl
      obtain ⟨e, he₁, he₂⟩ := hex
      exact ⟨e, ⟨he₁, he₂⟩, he e he₁ he₂⟩
  have hne : arities E f ≠ [] := by
    intro h0
    have := (hmem m).mpr rfl
    rw [h0] at this
    simp at this
  unfold kind reference
  have hreg : (!(arities E f).isEmpty) = true := by
    cases h : arities E f with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  have hlarger : (∃ a ∈ arities E f, n < a) ↔ n < m := by
    constructor
    · rintro ⟨a, ha, hlt⟩; rwa [(hmem a).mp ha] at hlt
    · intro hlt; exact ⟨m, (hmem m).mpr rfl, hlt⟩
  simp only [hreg, hmem n, hlarger, hne, Bool.true_eq_false, false_and, if_false, or_false]

/-- When every declaration of a call is of its arity, or every declaration of a
partial application is longer, every rule lets all of them govern it. -/
theorem eligible_all (R : Rule) (k : Kind) (n : ℕ) (ds : List Decl)
    (hk : k = .call ∨ k = .partialApp)
    (hcall : k = .call → ∀ d ∈ ds, d.arity = n)
    (hpart : k = .partialApp → ∀ d ∈ ds, n < d.arity) :
    eligible R k n ds = ds := by
  rcases hk with rfl | rfl
  · have h := hcall rfl
    have hfilter : (ds.filter fun d => decide (d.arity = n)) = ds :=
      List.filter_eq_self.mpr fun d hd => by simp [h d hd]
    cases R <;> simp only [eligible, hfilter]
    · exact List.filter_eq_self.mpr fun d hd => by simp [h d hd]
    · split_ifs with h0
      · rw [h0]; rfl
      · rfl
  · have h := hpart rfl
    cases R <;> simp only [eligible] <;>
      exact List.filter_eq_self.mpr fun d hd => by simp [le_of_lt (h d hd), h d hd]

/-- **The rules agree on names of one arity**: when a name's declarations and its
equations all have arity `m`, every rule gives every application of it the same
run. -/
theorem rules_agree_on_one_arity (pa : PartialAlternatives) (c : Bool) (E : List Eqn)
    (D : List Decl) (f m : ℕ) (args : List Arg)
    (hd : ∀ d ∈ declsOf D f, d.arity = m) (he : ∀ e ∈ E, e.name = f → e.arity = m)
    (hex : ∃ e ∈ E, e.name = f) (R : Rule) :
    apply ⟨R, pa, c⟩ ⟨E, D⟩ f args = apply ⟨.exact, pa, c⟩ ⟨E, D⟩ f args := by
  have hkind := kind_one_arity E f m args.length he hex
  have happ : ∀ R' : Rule, appKind R' ⟨E, D⟩ f args.length = kind E f args.length := by
    intro R'
    cases R' <;> try rfl
    simp only [appKind]
    split_ifs with hdecl
    · simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hdecl
      obtain ⟨-, d, hdD, hda⟩ := hdecl
      rw [hkind, if_pos (hda ▸ hd d hdD)]
    · rfl
  unfold apply
  simp only [happ]
  cases hk : kind E f args.length with
  | data => rfl
  | overapplied => rfl
  | call =>
      have hn : args.length = m := by
        rw [hkind] at hk; split_ifs at hk with h1; simp_all
      have hall : ∀ R' : Rule, eligible R' .call args.length (declsOf D f) = declsOf D f :=
        fun R' => eligible_all R' .call _ _ (Or.inl rfl) (fun _ d hdD => (hd d hdD).trans hn.symm)
          (fun h => absurd h (by decide))
      simp only [hall]
  | partialApp =>
      have hn : args.length < m := by
        rw [hkind] at hk; split_ifs at hk with h1 h2; simp_all
      have hall : ∀ R' : Rule, eligible R' .partialApp args.length (declsOf D f) = declsOf D f :=
        fun R' => eligible_all R' .partialApp _ _ (Or.inr rfl) (fun h => absurd h (by decide))
          (fun _ d hdD => (hd d hdD).symm ▸ hn)
      simp only [hall]

/-- Arguments that write nothing write nothing together. -/
theorem sum_writes_pure (as : List Arg) (h : ∀ a ∈ as, a.writes = 0) :
    (as.map Arg.writes).sum = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- A delivery gives a value for each argument. -/
theorem deliver_length {ts : List Ty} {as : List Arg} {vs : List Item} {w : ℕ}
    (h : deliver ts as = (some vs, w)) : vs.length = as.length := by
  induction as generalizing ts vs w with
  | nil =>
      cases ts with
      | nil => cases h; rfl
      | cons t ts => cases h; rfl
  | cons a as ih =>
      cases ts with
      | nil =>
          rw [deliver_nil_left] at h
          cases h
          exact List.length_map _
      | cons t ts =>
          rw [deliver_cons] at h
          split_ifs at h with hadm
          · obtain ⟨vs', hd, rfl⟩ := Option.map_eq_some_iff.mp (Prod.mk.inj h).1
            rw [List.length_cons, ih (Prod.ext hd rfl), List.length_cons]
          · exact absurd (Prod.mk.inj h).1 (by simp)

/-- Delivered values delivered again, as values, give the same values and write
nothing. -/
theorem deliver_values {ts : List Ty} {as : List Arg} {vs : List Item} {w : ℕ}
    (h : deliver ts as = (some vs, w)) : deliver ts (vs.map Arg.ofItem) = (some vs, 0) := by
  induction as generalizing ts vs w with
  | nil =>
      cases ts with
      | nil => cases h; rfl
      | cons t ts => cases h; rfl
  | cons a as ih =>
      cases ts with
      | nil =>
          rw [deliver_nil_left] at h
          cases h
          rw [deliver_nil_left]
          have hv : (((a :: as).map Arg.value).map Arg.ofItem).map Arg.value =
              (a :: as).map Arg.value := by
            simp [List.map_map, Function.comp_def, Arg.ofItem]
          have hw : ((((a :: as).map Arg.value).map Arg.ofItem).map Arg.writes).sum = 0 :=
            sum_writes_pure _ fun b hb => by
              obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
              rfl
          rw [hv, hw]
      | cons t ts =>
          rw [deliver_cons] at h
          split_ifs at h with hadm
          · obtain ⟨vs', hd, rfl⟩ := Option.map_eq_some_iff.mp (Prod.mk.inj h).1
            rw [List.map_cons, deliver_cons, pick_ofItem, cost_ofItem, if_pos hadm,
              ih (Prod.ext hd rfl)]
            rfl
          · exact absurd (Prod.mk.inj h).1 (by simp)

/-- Arguments that write nothing are delivered with no writes. -/
theorem deliver_writes_pure (ts : List Ty) (as : List Arg) (h : ∀ a ∈ as, a.writes = 0) :
    (deliver ts as).2 = 0 := by
  induction as generalizing ts with
  | nil => cases ts <;> rfl
  | cons a as ih =>
      cases ts with
      | nil =>
          rw [deliver_nil_left]
          exact sum_writes_pure _ h
      | cons t ts =>
          have hc : cost t a = 0 := cost_pure t a (h a List.mem_cons_self)
          have ih' := ih ts fun b hb => h b (List.mem_cons_of_mem a hb)
          rw [deliver_cons]
          split_ifs
          · simp [hc, ih']
          · exact hc

/-- Delivering two lists of arguments one after the other, when the first is
refused: the delivery stops there. -/
theorem deliver_append_none (ts : List Ty) (as bs : List Arg)
    (h : (deliver (ts.take as.length) as).1 = none) :
    deliver ts (as ++ bs) = (none, (deliver (ts.take as.length) as).2) := by
  induction as generalizing ts with
  | nil => cases ts <;> simp_all [deliver]
  | cons a as ih =>
      cases ts with
      | nil => simp [deliver_nil_left] at h
      | cons t ts =>
          simp only [List.length_cons, List.take_succ_cons] at h ⊢
          rw [List.cons_append, deliver_cons, deliver_cons]
          rw [deliver_cons] at h
          split_ifs at h ⊢ with hadm
          · have hn : (deliver (ts.take as.length) as).1 = none := by
              cases hd : (deliver (ts.take as.length) as).1 with
              | none => rfl
              | some _ => rw [hd] at h; simp at h
            rw [ih ts hn, hn]
            rfl
          · rfl

/-- Delivering two lists of arguments one after the other: the first by the
first inputs and, when it succeeds, the second by the rest. -/
theorem deliver_append_some (ts : List Ty) (as bs : List Arg) {vs : List Item} {w : ℕ}
    (h : deliver (ts.take as.length) as = (some vs, w)) :
    deliver ts (as ++ bs) =
      ((deliver (ts.drop as.length) bs).1.map (vs ++ ·), w + (deliver (ts.drop as.length) bs).2) := by
  induction as generalizing ts vs w with
  | nil =>
      cases ts with
      | nil =>
          cases h
          cases hd : deliver [] bs with
          | mk o x => cases o <;> simp_all
      | cons t ts =>
          cases h
          cases hd : deliver (t :: ts) bs with
          | mk o x => cases o <;> simp_all
  | cons a as ih =>
      cases ts with
      | nil =>
          rw [List.take_nil, deliver_nil_left] at h
          cases h
          simp [deliver_nil_left, List.map_append, List.sum_append, Nat.add_assoc]
      | cons t ts =>
          simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at h ⊢
          rw [deliver_cons] at h
          split_ifs at h with hadm
          · obtain ⟨vs', hd, rfl⟩ := Option.map_eq_some_iff.mp (Prod.mk.inj h).1
            have hw := (Prod.mk.inj h).2
            rw [List.cons_append, deliver_cons, if_pos hadm,
              ih ts (Prod.ext hd rfl), ← hw]
            cases (deliver (ts.drop as.length) bs).1 <;> simp [Nat.add_assoc]
          · exact absurd (Prod.mk.inj h).1 (by simp)

/-- A typed alternative of a call whose first arguments its declaration refuses
answers nothing, with the writes made before the refusal. -/
theorem typedCall_refused (E : List Eqn) (f : ℕ) (d : Decl) (as bs : List Arg)
    (h : (deliver (d.inputs.take as.length) as).1 = none) :
    typedCall E f d (as ++ bs) = ([], (deliver (d.inputs.take as.length) as).2) := by
  unfold typedCall
  rw [deliver_append_none _ _ _ h]

/-- A typed alternative of a call whose first arguments were delivered once
already: the same answers, without their writes. -/
theorem typedCall_values (E : List Eqn) (f : ℕ) (d : Decl) (as bs : List Arg) {vs : List Item}
    {w : ℕ} (h : deliver (d.inputs.take as.length) as = (some vs, w)) :
    (typedCall E f d (vs.map Arg.ofItem ++ bs)).1 = (typedCall E f d (as ++ bs)).1 ∧
      (typedCall E f d (as ++ bs)).2 = (typedCall E f d (vs.map Arg.ofItem ++ bs)).2 + w := by
  have hlen : (vs.map Arg.ofItem).length = as.length := by
    rw [List.length_map]; exact deliver_length h
  have h' : deliver (d.inputs.take (vs.map Arg.ofItem).length) (vs.map Arg.ofItem) =
      (some vs, 0) := by
    rw [hlen]; exact deliver_values h
  unfold typedCall
  rw [deliver_append_some _ _ _ h, deliver_append_some _ _ _ h', hlen]
  cases (deliver (d.inputs.drop as.length) bs).1 with
  | none => exact ⟨rfl, by show w + _ = 0 + _ + w; omega⟩
  | some ys => exact ⟨rfl, by show w + _ + _ = 0 + _ + _ + w; omega⟩

theorem sum_map_fst_congr {α : Type} (l : List α) (k₁ k₂ : α → Run)
    (h : ∀ x ∈ l, (k₁ x).1 = (k₂ x).1) : (Run.sum (l.map k₁)).1 = (Run.sum (l.map k₂)).1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.map_cons, Run.sum]
      rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem x hy)]

theorem sum_map_snd_shift {α : Type} (l : List α) (k₁ k₂ : α → Run) (w : ℕ)
    (h : ∀ x ∈ l, (k₁ x).2 = (k₂ x).2 + w) :
    (Run.sum (l.map k₁)).2 = (Run.sum (l.map k₂)).2 + l.length * w := by
  induction l with
  | nil => simp [Run.sum]
  | cons x l ih =>
      simp only [List.map_cons, Run.sum, List.length_cons]
      rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem x hy)]
      ring

theorem sum_map_refused {α : Type} (l : List α) (k : α → Run) (w : ℕ)
    (h : ∀ x ∈ l, k x = ([], w)) : Run.sum (l.map k) = ([], l.length * w) := by
  induction l with
  | nil => simp [Run.sum]
  | cons x l ih =>
      simp only [List.map_cons, Run.sum, List.length_cons]
      rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem x hy)]
      refine Prod.ext rfl ?_
      show w + l.length * w = (l.length + 1) * w
      ring

theorem dedup_eq_singleton {α : Type} [DecidableEq α] {l : List α} {p : α} (hne : l ≠ [])
    (h : ∀ x ∈ l, x = p) : l.dedup = [p] := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a l ih =>
      have ha : a = p := h a List.mem_cons_self
      subst ha
      by_cases hl : l = []
      · subst hl
        rw [List.dedup_cons_of_notMem (by simp), List.dedup_nil]
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
        have hmem : a ∈ l := by
          rw [← h x (List.mem_cons_of_mem a hx)]; exact hx
        rw [List.dedup_cons_of_mem hmem, ih hl fun y hy => h y (List.mem_cons_of_mem a hy)]

theorem Run.sum_singleton (r : Run) : Run.sum [r] = r := by
  obtain ⟨a, b⟩ := r
  simp [Run.sum]

theorem throughVariable_eq (S : Semantics) (P : Program) (f : ℕ) (as bs : List Arg) :
    throughVariable S P f as bs =
      ((Run.sum ((apply S P f as).1.map fun v => complete S P v bs)).1,
        (apply S P f as).2 + (Run.sum ((apply S P f as).1.map fun v => complete S P v bs)).2) :=
  rfl

theorem apply_proposed_call (E : List Eqn) (D : List Decl) (f : ℕ) (args : List Arg)
    (hk : kind E f args.length = .call) :
    apply exactPerPlan ⟨E, D⟩ f args =
      if (eligible .exact .call args.length (declsOf D f)).dedup = [] then untypedCall E f args
      else Run.sum ((eligible .exact .call args.length (declsOf D f)).dedup.map
        fun d => typedCall E f d args) := by
  unfold apply
  simp only [exactPerPlan, appKind, hk]
  rfl

theorem apply_proposed_partial (E : List Eqn) (D : List Decl) (f : ℕ) (args : List Arg)
    (hk : kind E f args.length = .partialApp) :
    apply exactPerPlan ⟨E, D⟩ f args =
      if eligible .exact .partialApp args.length (declsOf D f) = [] then
        ([.partialApp f (args.map Arg.value)], (args.map Arg.writes).sum)
      else Run.sum (((eligible .exact .partialApp args.length (declsOf D f)).map
          fun d => d.inputs.take args.length).dedup.map
            fun p => typedPartial f p .undef false args) := by
  unfold apply
  simp only [exactPerPlan, appKind, hk]
  rfl

/-- **Completing a partial application through a variable answers as the complete
call** (`exactPerPlan`), when the longer declarations agree on the supplied positions
and the completed arity is typed or no declaration is longer than the partial
application.  Its writes are the complete call's when the supplied arguments
write nothing or the completed arity has at most one distinct declaration. -/
theorem exactPerPlan_completion (E : List Eqn) (D : List Decl) (f : ℕ) (as bs : List Arg)
    (hpart : kind E f as.length = .partialApp)
    (hcall : kind E f (as.length + bs.length) = .call)
    (hagree : ∀ d₁ ∈ declsOf D f, ∀ d₂ ∈ declsOf D f, as.length < d₁.arity →
        as.length < d₂.arity → d₁.inputs.take as.length = d₂.inputs.take as.length)
    (htyped : (∃ d ∈ declsOf D f, d.arity = as.length + bs.length) ∨
        ∀ d ∈ declsOf D f, d.arity ≤ as.length) :
    (throughVariable exactPerPlan ⟨E, D⟩ f as bs).1 = (apply exactPerPlan ⟨E, D⟩ f (as ++ bs)).1 ∧
      (((∀ a ∈ as, a.writes = 0) ∨
          (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup.length ≤ 1) →
        (throughVariable exactPerPlan ⟨E, D⟩ f as bs).2 = (apply exactPerPlan ⟨E, D⟩ f (as ++ bs)).2) := by
  have hkn : as.length < as.length + bs.length := by
    rcases Nat.eq_zero_or_pos bs.length with h0 | h0
    · rw [h0, Nat.add_zero, hpart] at hcall; cases hcall
    · omega
  have hfull := apply_proposed_call E D f (as ++ bs) (by rw [List.length_append]; exact hcall)
  rw [List.length_append] at hfull
  have hstep := apply_proposed_partial E D f as hpart
  rcases htyped with ⟨d₀, hd₀, hd₀n⟩ | hall
  · -- the completed arity is typed
    have hd₀L : d₀ ∈ eligible .exact .partialApp as.length (declsOf D f) := by
      simp only [eligible, List.mem_filter, decide_eq_true_eq]; exact ⟨hd₀, hd₀n ▸ hkn⟩
    have hLne : eligible .exact .partialApp as.length (declsOf D f) ≠ [] :=
      List.ne_nil_of_mem hd₀L
    have hplans : ((eligible .exact .partialApp as.length (declsOf D f)).map
        fun d => d.inputs.take as.length).dedup = [d₀.inputs.take as.length] := by
      apply dedup_eq_singleton
      · simp [hLne]
      · intro x hx
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
        simp only [eligible, List.mem_filter, decide_eq_true_eq] at hd
        exact hagree d hd.1 d₀ hd₀ hd.2 (hd₀n ▸ hkn)
    have hd₀M : d₀ ∈ eligible .exact .call (as.length + bs.length) (declsOf D f) := by
      simp only [eligible, List.mem_filter, decide_eq_true_eq]; exact ⟨hd₀, hd₀n⟩
    have hMne : (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup ≠ [] := by
      rw [Ne, List.dedup_eq_nil]; exact List.ne_nil_of_mem hd₀M
    have hone : (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup.length ≤ 1 →
        (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup.length = 1 := by
      have := List.length_pos_of_ne_nil hMne; omega
    have htake : ∀ d ∈ (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup,
        d.inputs.take as.length = d₀.inputs.take as.length := by
      intro d hd
      rw [List.mem_dedup] at hd
      simp only [eligible, List.mem_filter, decide_eq_true_eq] at hd
      exact hagree d hd.1 d₀ hd₀ (hd.2 ▸ hkn) (hd₀n ▸ hkn)
    cases hdp : deliver (d₀.inputs.take as.length) as with
    | mk o w =>
      have hpure : (∀ a ∈ as, a.writes = 0) → w = 0 := by
        intro hp
        have := deliver_writes_pure (d₀.inputs.take as.length) as hp
        rw [hdp] at this; exact this
      cases o with
      | none =>
          have hrefused : ∀ d ∈ (eligible .exact .call (as.length + bs.length)
              (declsOf D f)).dedup, typedCall E f d (as ++ bs) = ([], w) := by
            intro d hd
            rw [typedCall_refused E f d as bs (by rw [htake d hd, hdp]), htake d hd, hdp]
          have hpstep : apply exactPerPlan ⟨E, D⟩ f as = ([], w) := by
            rw [hstep, if_neg hLne, hplans, List.map_cons, List.map_nil, Run.sum_singleton]
            unfold typedPartial
            rw [hdp]
          have hthrough : throughVariable exactPerPlan ⟨E, D⟩ f as bs = ([], w) := by
            rw [throughVariable_eq, hpstep]
            rfl
          rw [hthrough, hfull, if_neg hMne, sum_map_refused _ _ _ hrefused]
          refine ⟨rfl, fun hw => ?_⟩
          rcases hw with hp | h1
          · rw [hpure hp]; simp
          · rw [hone h1]; simp
      | some vs =>
          have hvs := deliver_length hdp
          have hcomp : apply exactPerPlan ⟨E, D⟩ f (vs.map Arg.ofItem ++ bs) =
              Run.sum ((eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup.map
                fun d => typedCall E f d (vs.map Arg.ofItem ++ bs)) := by
            have h := apply_proposed_call E D f (vs.map Arg.ofItem ++ bs)
              (by rw [List.length_append, List.length_map, hvs]; exact hcall)
            rw [List.length_append, List.length_map, hvs, if_neg hMne] at h
            exact h
          have hvals : ∀ d ∈ (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup,
              (typedCall E f d (vs.map Arg.ofItem ++ bs)).1 = (typedCall E f d (as ++ bs)).1 ∧
                (typedCall E f d (as ++ bs)).2 =
                  (typedCall E f d (vs.map Arg.ofItem ++ bs)).2 + w := by
            intro d hd
            exact typedCall_values E f d as bs (by rw [htake d hd, hdp])
          have hpstep : apply exactPerPlan ⟨E, D⟩ f as = ([.partialApp f vs], w) := by
            rw [hstep, if_neg hLne, hplans, List.map_cons, List.map_nil, Run.sum_singleton]
            unfold typedPartial
            rw [hdp]
            rfl
          have hthrough : throughVariable exactPerPlan ⟨E, D⟩ f as bs =
              ((apply exactPerPlan ⟨E, D⟩ f (vs.map Arg.ofItem ++ bs)).1,
                w + (apply exactPerPlan ⟨E, D⟩ f (vs.map Arg.ofItem ++ bs)).2) := by
            rw [throughVariable_eq, hpstep, List.map_cons, List.map_nil, Run.sum_singleton]
            rfl
          rw [hthrough, hcomp, hfull, if_neg hMne]
          refine ⟨sum_map_fst_congr _ _ _ fun d hd => (hvals d hd).1, fun hw => ?_⟩
          rw [sum_map_snd_shift _ _ _ w fun d hd => (hvals d hd).2]
          rcases hw with hp | h1
          · rw [hpure hp]; simp
          · rw [hone h1]; ring
  · -- no declaration is longer than the partial application
    have hL : eligible .exact .partialApp as.length (declsOf D f) = [] := by
      simp only [eligible, List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
      exact hall
    have hM : (eligible .exact .call (as.length + bs.length) (declsOf D f)).dedup = [] := by
      rw [List.dedup_eq_nil]
      simp only [eligible, List.filter_eq_nil_iff, decide_eq_true_eq]
      intro d hd hdn
      have := hall d hd; omega
    have hcomp := apply_proposed_call E D f ((as.map Arg.value).map Arg.ofItem ++ bs)
      (by rw [List.length_append, List.length_map, List.length_map]; exact hcall)
    rw [List.length_append, List.length_map, List.length_map, if_pos hM] at hcomp
    have hpstep : apply exactPerPlan ⟨E, D⟩ f as =
        ([.partialApp f (as.map Arg.value)], (as.map Arg.writes).sum) := by
      rw [hstep, if_pos hL]
    have hthrough : throughVariable exactPerPlan ⟨E, D⟩ f as bs =
        ((apply exactPerPlan ⟨E, D⟩ f ((as.map Arg.value).map Arg.ofItem ++ bs)).1,
          (as.map Arg.writes).sum +
            (apply exactPerPlan ⟨E, D⟩ f ((as.map Arg.value).map Arg.ofItem ++ bs)).2) := by
      rw [throughVariable_eq, hpstep, List.map_cons, List.map_nil, Run.sum_singleton]
      rfl
    have hv : ((as.map Arg.value).map Arg.ofItem ++ bs).map Arg.value =
        (as ++ bs).map Arg.value := by
      simp [List.map_append, List.map_map, Function.comp_def, Arg.ofItem]
    have hw0 : (((as.map Arg.value).map Arg.ofItem).map Arg.writes).sum = 0 :=
      sum_writes_pure _ fun b hb => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
        rfl
    have hw : (((as.map Arg.value).map Arg.ofItem ++ bs).map Arg.writes).sum =
        (bs.map Arg.writes).sum := by
      rw [List.map_append, List.sum_append, hw0, Nat.zero_add]
    rw [hthrough, hcomp, hfull, if_pos hM]
    unfold untypedCall
    rw [hv, hw]
    refine ⟨rfl, fun _ => ?_⟩
    simp only [List.map_append, List.sum_append]
    omega

namespace Controls

/-! ## Controls: the measured programs -/

/-- An argument whose source and value are the symbol `s`. -/
def symArg (s : ℕ) : Arg := Arg.ofItem (.sym s)

/-- An argument whose source and value are the number `n`. -/
def numArg (n : ℕ) : Arg := Arg.ofItem (.num n)

/-- `(+ 1 2)`: held as written, `3` when evaluated. -/
def plus12 : Arg := ⟨.src 12, .num 3, 0⟩

/-- `touch`: `(-> Atom %Undefined%)`, `(-> Atom Atom %Undefined%)`, a unary
equation that writes once and answers nothing, a binary one unused. -/
def touch : Program where
  eqns := [⟨0, 1, fun _ => ([], 1)⟩, ⟨0, 2, fun _ => ([.item (.sym 9)], 0)⟩]
  decls := [⟨0, [.atom], .undef⟩, ⟨0, [.atom, .atom], .undef⟩]

/-- Stable-fixed `c3adb86`: `(touch z)` writes twice. -/
theorem touch_c3adb86 : apply c3adb86Written touch 0 [symArg 1] = ([], 2) := by decide +kernel

/-- CeTTa: `(touch z)` writes once. -/
theorem touch_cetta : apply cettaToday touch 0 [symArg 1] = ([], 1) := by decide +kernel

/-- The exactPerPlan semantics: `(touch z)` writes once. -/
theorem touch_exactPerPlan : apply exactPerPlan touch 0 [symArg 1] = ([], 1) := by decide +kernel

/-- `md`, from SWI-PeTTa's own fixture: `(-> Number Number)`,
`(-> Number Number Number)`, `(= (md $x) $x)`, `(= (md $x $y) $y)`. -/
def md : Program where
  eqns := [⟨1, 1, fun vs => ((vs.take 1).map .item, 0)⟩,
    ⟨1, 2, fun vs => ((vs.drop 1).map .item, 0)⟩]
  decls := [⟨1, [.number], .number⟩, ⟨1, [.number, .number], .number⟩]

/-- Stable-fixed `c3adb86`: `(md 1)` answers twice; its fixture never calls it. -/
theorem md_unary_c3adb86 :
    (apply c3adb86Written md 1 [numArg 1]).1 = [.item (.num 1), .item (.num 1)] := by decide +kernel

/-- CeTTa: `(md 1)` answers once. -/
theorem md_unary_cetta : (apply cettaToday md 1 [numArg 1]).1 = [.item (.num 1)] := by
  decide +kernel

/-- The exactPerPlan semantics: `(md 1)` answers once. -/
theorem md_unary_exactPerPlan : (apply exactPerPlan md 1 [numArg 1]).1 = [.item (.num 1)] := by
  decide +kernel

/-- Every semantics: `(md 1 2)` answers `2` once. -/
theorem md_binary :
    (apply c3adb86Written md 1 [numArg 1, numArg 2]).1 = [.item (.num 2)] ∧
    (apply cettaToday md 1 [numArg 1, numArg 2]).1 = [.item (.num 2)] ∧
    (apply exactPerPlan md 1 [numArg 1, numArg 2]).1 = [.item (.num 2)] := by decide +kernel

/-- `b1`: `(-> Number Number Number)` alone and `(= (b1 $x) value)`. -/
def b1 : Program where
  eqns := [⟨2, 1, fun _ => ([.item (.sym 7)], 0)⟩]
  decls := [⟨2, [.number, .number], .number⟩]

/-- A binary declaration alone rejects the unary call on SWI-PeTTa (`()`), and
leaves it untyped elsewhere (`(value)`). -/
theorem b1_unary :
    (apply c3adb86Written b1 2 [numArg 1]).1 = [] ∧
    (apply cettaToday b1 2 [numArg 1]).1 = [.item (.sym 7)] ∧
    (apply exactPerPlan b1 2 [numArg 1]).1 = [.item (.sym 7)] := by decide +kernel

/-- `b2`: `(-> Number Number)`, `(-> Number Number Bool)`, and a unary equation
answering `True`. -/
def b2 : Program where
  eqns := [⟨3, 1, fun _ => ([.item (.truth true)], 0)⟩]
  decls := [⟨3, [.number], .number⟩, ⟨3, [.number, .number], .bool⟩]

/-- SWI-PeTTa checks the unary call's answer against the binary declaration's
result type: `True` passes only as a `Bool`, a type no declaration gives the
unary call. -/
theorem b2_unary :
    (apply c3adb86Written b2 3 [numArg 1]).1 = [.item (.truth true)] ∧
    (apply cettaToday b2 3 [numArg 1]).1 = [] ∧
    (apply exactPerPlan b2 3 [numArg 1]).1 = [] := by decide +kernel

/-- `tr`: `(-> Atom %Undefined%)`, `(-> Atom Atom %Undefined%)`, a unary equation
answering its argument. -/
def tr : Program where
  eqns := [⟨4, 1, fun vs => (vs.map .item, 0)⟩]
  decls := [⟨4, [.atom], .undef⟩, ⟨4, [.atom, .atom], .undef⟩]

/-- SWI-PeTTa's routes split: the written `(tr (+ 1 2))` answers the held
argument twice, the same call through a variable answers its value once. -/
theorem tr_routes_c3adb86 :
    (apply c3adb86Written tr 4 [plus12]).1 = [.item (.src 12), .item (.src 12)] ∧
    (c3adb86Dynamic tr 4 [plus12]).1 = [.item (.num 3)] := by decide +kernel

/-- The exactPerPlan semantics and CeTTa: one held answer, on every route. -/
theorem tr_exactPerPlan :
    (apply exactPerPlan tr 4 [plus12]).1 = [.item (.src 12)] ∧
    (apply cettaToday tr 4 [plus12]).1 = [.item (.src 12)] := by decide +kernel

/-- `a13`: declarations of one, two and three inputs, all `Atom`, and a unary
equation. -/
def a13 : Program where
  eqns := [⟨5, 1, fun vs => (vs.map .item, 0)⟩]
  decls := [⟨5, [.atom], .undef⟩, ⟨5, [.atom, .atom], .undef⟩, ⟨5, [.atom, .atom, .atom], .undef⟩]

/-- SWI-PeTTa answers once per declaration with at least one input. -/
theorem a13_unary :
    (apply c3adb86Written a13 5 [plus12]).1 = [.item (.src 12), .item (.src 12), .item (.src 12)] ∧
    (apply exactPerPlan a13 5 [plus12]).1 = [.item (.src 12)] := by decide +kernel

/-- The short and long forms of an operation, as the transform library declares
them: `(-> Atom Atom %Undefined%)`, `(-> Atom Atom Atom %Undefined%)`, with
equations at both arities. -/
def pc : Program where
  eqns := [⟨6, 2, fun vs => ([.data 50 vs], 0)⟩, ⟨6, 3, fun vs => ([.data 51 vs], 0)⟩]
  decls := [⟨6, [.atom, .atom], .undef⟩, ⟨6, [.atom, .atom, .atom], .undef⟩]

/-- The short form answers twice on SWI-PeTTa, once elsewhere. -/
theorem pc_written :
    (apply c3adb86Written pc 6 [symArg 1, plus12]).1 =
      [.data 50 [.sym 1, .src 12], .data 50 [.sym 1, .src 12]] ∧
    (apply cettaToday pc 6 [symArg 1, plus12]).1 = [.data 50 [.sym 1, .src 12]] ∧
    (apply exactPerPlan pc 6 [symArg 1, plus12]).1 = [.data 50 [.sym 1, .src 12]] := by
  decide +kernel

/-- Completing `(pc x)` through a variable: CeTTa makes a partial value per
longer declaration and answers twice; SWI-PeTTa also makes two and completes
them without the declarations; the exactPerPlan semantics answers as the written
call. -/
theorem pc_through_variable :
    (throughVariable cettaToday pc 6 [symArg 1] [plus12]).1 =
      [.data 50 [.sym 1, .src 12], .data 50 [.sym 1, .src 12]] ∧
    (c3adb86ThroughVariable pc 6 [symArg 1] [plus12]).1 =
      [.data 50 [.sym 1, .num 3], .data 50 [.sym 1, .num 3]] ∧
    (throughVariable exactPerPlan pc 6 [symArg 1] [plus12]).1 = [.data 50 [.sym 1, .src 12]] := by
  decide +kernel

/-- `atLeast` on every route: completing `(pc x)` through a variable answers four
times (two partial values, each completed under both declarations), where the
written call answers twice. -/
theorem atLeast_every_route_multiplies :
    (throughVariable c3adb86Written pc 6 [symArg 1] [plus12]).1.length = 4 ∧
    (apply c3adb86Written pc 6 [symArg 1, plus12]).1.length = 2 := by decide +kernel

/-- `p1`: `(-> %Undefined% %Undefined%)` and a binary equation only. -/
def p1 : Program where
  eqns := [⟨7, 2, fun vs => ([.data 52 vs], 0)⟩]
  decls := [⟨7, [.undef], .undef⟩]

/-- `(p1 1)` is a partial application by its equations' arities.  CeTTa reads
the unary declaration as making it a call, and answers nothing. -/
theorem p1_unary :
    (apply c3adb86Written p1 7 [numArg 1]).1 = [.partialApp 7 [.num 1]] ∧
    (apply cettaToday p1 7 [numArg 1]).1 = [] ∧
    (apply exactPerPlan p1 7 [numArg 1]).1 = [.partialApp 7 [.num 1]] := by decide +kernel

/-- `o2`: `(-> Atom Atom %Undefined%)` and a unary equation only. -/
def o2 : Program where
  eqns := [⟨8, 1, fun vs => ([.data 53 vs], 0)⟩]
  decls := [⟨8, [.atom, .atom], .undef⟩]

/-- `(o2 a b)` is an over-application by its equations' arities.  CeTTa answers
nothing. -/
theorem o2_binary :
    (apply c3adb86Written o2 8 [symArg 1, symArg 2]).1 = [.overapplied 8] ∧
    (apply cettaToday o2 8 [symArg 1, symArg 2]).1 = [] ∧
    (apply exactPerPlan o2 8 [symArg 1, symArg 2]).1 = [.overapplied 8] := by decide +kernel

/-- `c9`: longer declarations that disagree at the first position,
`(-> Atom Atom %Undefined%)` and `(-> %Undefined% Atom Atom %Undefined%)`, with
equations at two and three arguments. -/
def c9 : Program where
  eqns := [⟨9, 2, fun vs => ([.data 60 vs], 0)⟩, ⟨9, 3, fun vs => ([.data 61 vs], 0)⟩]
  decls := [⟨9, [.atom, .atom], .undef⟩, ⟨9, [.undef, .atom, .atom], .undef⟩]

/-- When the longer declarations disagree on the supplied positions, the
partial application has two values and its completion answers twice, where
the written call answers once (measured on CeTTa as well). -/
theorem disagreeing_plans_complete_differently :
    (throughVariable exactPerPlan c9 9 [plus12] [symArg 2]).1 =
      [.data 60 [.src 12, .sym 2], .data 60 [.num 3, .sym 2]] ∧
    (apply exactPerPlan c9 9 [plus12, symArg 2]).1 = [.data 60 [.src 12, .sym 2]] ∧
    (throughVariable cettaToday c9 9 [plus12] [symArg 2]).1 =
      [.data 60 [.src 12, .sym 2], .data 60 [.num 3, .sym 2]] := by decide +kernel

/-- An argument written `(let $_ (add-atom &self w) 1)`: its value is `1`, and
evaluating it writes once. -/
def writing1 : Arg := ⟨.src 13, .num 1, 1⟩

/-- `e2`: two binary declarations agreeing at the first position,
`(-> %Undefined% Atom %Undefined%)` and `(-> %Undefined% Atom Atom)`. -/
def e2 : Program where
  eqns := [⟨10, 2, fun vs => ([.data 70 vs], 0)⟩]
  decls := [⟨10, [.undef, .atom], .undef⟩, ⟨10, [.undef, .atom], .atom⟩]

/-- Each alternative of the written call evaluates its own arguments: two
answers, two writes.  The exactPerPlan partial application evaluates its argument
once, and its completion answers twice: the same answers, one write.  CeTTa
makes a partial value per declaration and completes each under both: four
answers, two writes (measured). -/
theorem partial_writes_once :
    apply exactPerPlan e2 10 [writing1, symArg 2] =
      ([.data 70 [.num 1, .sym 2], .data 70 [.num 1, .sym 2]], 2) ∧
    throughVariable exactPerPlan e2 10 [writing1] [symArg 2] =
      ([.data 70 [.num 1, .sym 2], .data 70 [.num 1, .sym 2]], 1) ∧
    throughVariable cettaToday e2 10 [writing1] [symArg 2] =
      ([.data 70 [.num 1, .sym 2], .data 70 [.num 1, .sym 2],
        .data 70 [.num 1, .sym 2], .data 70 [.num 1, .sym 2]], 2) := by decide +kernel

/-- `q`: the two binary declarations of `e2` and one ternary declaration, all
evaluating the first argument, with equations at two and three arguments. -/
def q : Program where
  eqns := [⟨11, 2, fun vs => ([.data 80 vs], 0)⟩, ⟨11, 3, fun vs => ([.data 81 vs], 0)⟩]
  decls := [⟨11, [.undef, .atom], .undef⟩, ⟨11, [.undef, .atom], .atom⟩,
    ⟨11, [.undef, .atom, .atom], .undef⟩]

/-- The written binary call writes twice, the written ternary call once. -/
theorem q_written_writes :
    (apply exactPerPlan q 11 [writing1, symArg 2]).2 = 2 ∧
    (apply exactPerPlan q 11 [writing1, symArg 2, symArg 3]).2 = 1 := by decide +kernel

/-- `l5`: one longer declaration `(-> Atom Atom %Undefined%)` and a unary
equation answering its argument. -/
def l5 : Program where
  eqns := [⟨12, 1, fun vs => (vs.map .item, 0)⟩]
  decls := [⟨12, [.atom, .atom], .undef⟩]

/-- `exactElseLonger` is not monotone: adding the exact `(-> %Undefined% %Undefined%)`
removes the longer declaration's held answer. -/
theorem exactElseLonger_not_monotone :
    .item (.src 12) ∈ (apply ⟨.exactElseLonger, .perPlan, false⟩ l5 12 [plus12]).1 ∧
    .item (.src 12) ∉ (apply ⟨.exactElseLonger, .perPlan, false⟩
      ⟨l5.eqns, ⟨12, [.undef], .undef⟩ :: l5.decls⟩ 12 [plus12]).1 := by decide +kernel

/-- `a5`: `(-> %Undefined% Atom %Undefined%)` and a binary equation. -/
def a5 : Program where
  eqns := [⟨13, 2, fun vs => ([.data 54 vs], 0)⟩]
  decls := [⟨13, [.undef, .atom], .undef⟩]

/-- `declaredArityIsCall` is not monotone: adding `(-> Atom %Undefined%)` makes
the unary application a call with no equation, removing the partial value. -/
theorem declaredArityIsCall_not_monotone :
    (apply cettaToday a5 13 [plus12]).1 = [.partialApp 13 [.num 3]] ∧
    (apply cettaToday ⟨a5.eqns, ⟨13, [.atom], .undef⟩ :: a5.decls⟩ 13 [plus12]).1 = [] := by
  decide +kernel

/-- `atLeast` is not local: adding the binary declaration of `touch` changes its
unary call, which now writes twice. -/
theorem atLeast_not_local :
    apply c3adb86Written ⟨touch.eqns, [⟨0, [.atom], .undef⟩]⟩ 0 [symArg 1] = ([], 1) ∧
    apply c3adb86Written touch 0 [symArg 1] = ([], 2) := by decide +kernel

/-- `exactElseLonger` is not local: a binary declaration added to a name without
declarations takes over its unary call. -/
theorem exactElseLonger_not_local :
    (apply ⟨.exactElseLonger, .perPlan, false⟩ ⟨b1.eqns, []⟩ 2 [numArg 1]).1 = [.item (.sym 7)] ∧
    (apply ⟨.exactElseLonger, .perPlan, false⟩ b1 2 [numArg 1]).1 = [] := by decide +kernel

/-- Declarations of one arity do not make the rules agree when the equations
have another: `b1`'s binary declaration and unary equation. -/
theorem one_declared_arity_disagrees :
    apply ⟨.atLeast, .perPlan, false⟩ b1 2 [numArg 1] ≠
      apply ⟨.exact, .perPlan, false⟩ b1 2 [numArg 1] := by decide +kernel

end Controls

/-- **No partial step can match both completions' writes.**  A partial
application evaluates its supplied arguments before it knows how many more
arguments it will get, and its completion passes them on as values, which
write nothing.  In `Controls.q` the written binary call writes twice and the
written ternary call once; whatever the partial step writes, the completed
binary and ternary calls through a variable cannot both write what the written
calls write. -/
theorem partial_writes_cannot_match_both (stepWrites : ℕ) :
    ¬ (stepWrites = (apply exactPerPlan Controls.q 11
          [Controls.writing1, Controls.symArg 2]).2 ∧
       stepWrites = (apply exactPerPlan Controls.q 11
          [Controls.writing1, Controls.symArg 2, Controls.symArg 3]).2) := by
  rw [Controls.q_written_writes.1, Controls.q_written_writes.2]
  omega

end Mettapedia.Machines.DeclarationArity
