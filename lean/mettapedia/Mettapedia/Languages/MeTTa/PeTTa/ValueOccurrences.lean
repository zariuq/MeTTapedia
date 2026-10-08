import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Value occurrences: environments, substitution and plans

PeTTa compiles a source variable to a Prolog variable.  An occurrence of the
variable denotes the value bound to it, and that value is never evaluated
again.  A machine may realize this in two ways:

* keep the syntax and an environment, reading each variable occurrence as the
  value it holds (`evalIn`);
* substitute the values into the syntax and evaluate the result under the
  plan compiled from the syntax, which marks each variable occurrence as a
  value (`evalPlanned` with `planOf`).

`evalPlanned_planOf_subst` proves the two agree.  An application of
`(|-> ($x) body)` may also rename `$x` to a fresh variable bound to the
argument; `evalIn_open_fresh` proves that exact, and `open_captured_differs`
shows the freshness it needs.  What does not agree is the
third reading: substitute, then evaluate the result as code, deciding every
occurrence from the substituted term itself.  That is evaluation of
`subst σ t` in the empty environment, and a substituted value that spells a
call is called again (`evalCode_subst_evaluates_again`).  It agrees only when
every substituted value is inert (`evalCode_subst_of_inert`), as every value
none of whose expressions the program calls is (`DataOnly.inert`).

Answers are bags, as lists: an expression's children are evaluated in order,
every choice of one answer per child is formed, and each is then called or
kept as data.  The program is abstract: it says which evaluated expressions
are calls and what their answers are.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

/-- What a program says about an evaluated expression: whether it is a call,
and the answers of that call, which are values. -/
structure Program where
  isCall : List Atom → Bool
  answers : List Atom → List Atom

/-- Every choice of one answer per child, in order. -/
def choices : List (List Atom) → List (List Atom)
  | [] => [[]]
  | answers :: rest => answers.flatMap fun a => (choices rest).map (a :: ·)

/-- An evaluated expression is called, or else kept as data. -/
def finish (P : Program) (items : List Atom) : List Atom :=
  if P.isCall items then P.answers items else [.expression items]

/-- Evaluation of syntax in an environment.  A variable occurrence is the
value bound to it, or the variable itself when unbound; neither is evaluated
again. -/
def evalIn (P : Program) (σ : Subst) : Atom → List Atom
  | .var v => [(σ v).getD (.var v)]
  | .expression es => (choices (evalList P σ es)).flatMap (finish P)
  | .symbol s => [.symbol s]
  | .grounded g => [.grounded g]
where
  evalList (P : Program) (σ : Subst) : List Atom → List (List Atom)
    | [] => []
    | a :: as => evalIn P σ a :: evalList P σ as

/-- The variable-occurrence view agrees with an actual executable path,
including captured expressions whose heads name runnable functions. The
abstract call interface is immaterial for a value occurrence. -/
theorem executable_variable_matches_view (program : SpaceSemantics.Program)
    (view : Program) (state : Effects.State)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String) :
    Eval.Returns program bindings state (.var name) state
      (evalIn view (bindings.lookup) (.var name)) := by
  simpa only [evalIn, Mettapedia.Languages.ProcessCalculi.MORK.applySubst] using
    Eval.variable_returns program bindings state name

/-- The same observation is a finite whole-program derivation over the shared
store, not merely a comparison between two occurrence-view evaluators. -/
theorem executable_variable_derivation (program : SpaceSemantics.Program)
    (view : Program) (state : Effects.State)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String) :
    DeclarativeSpec.Runs program { state, control := .evaluate bindings (.var name) }
      (.complete state (evalIn view bindings.lookup (.var name)) [] []) :=
  (Eval.completed_derivation_iff_path program _ state _ [] []).mpr
    (executable_variable_matches_view program view state bindings name)

/-- Evaluation as code: every occurrence is decided from the term itself.
Applied to a term into which values were substituted, this is the planless
reading, which evaluates those values again. -/
abbrev evalCode (P : Program) : Atom → List Atom :=
  evalIn P SubstitutionAlgebra.empty

/-- The plan of an occurrence: a value, returned as it stands, or code, whose
children are evaluated under their own plans before the expression is called
or kept as data. -/
inductive Plan where
  | value : Plan
  | code : List Plan → Plan

/-- Evaluation under a plan.  A child without a plan of its own is evaluated
as code. -/
def evalPlanned (P : Program) : Plan → Atom → List Atom
  | .value, a => [a]
  | .code plans, .expression es =>
      (choices (evalPlannedList P plans es)).flatMap (finish P)
  | .code _, .var v => [.var v]
  | .code _, .symbol s => [.symbol s]
  | .code _, .grounded g => [.grounded g]
where
  evalPlannedList (P : Program) : List Plan → List Atom → List (List Atom)
    | plan :: plans, a :: as => evalPlanned P plan a :: evalPlannedList P plans as
    | [], a :: as => evalCode P a :: evalPlannedList P [] as
    | _, [] => []

/-- The plan compiled from syntax: each variable occurrence is a value, and
everything else is code. -/
def planOf : Atom → Plan
  | .var _ => .value
  | .expression es => .code (planOfList es)
  | .symbol _ => .code []
  | .grounded _ => .code []
where
  planOfList : List Atom → List Plan
    | [] => []
    | a :: as => planOf a :: planOfList as

/-! ## Substitution under the syntax's own plan -/

/-- Substituting an environment into syntax and evaluating the result under
the plan compiled from the syntax is evaluation of the syntax in the
environment. -/
theorem evalPlanned_planOf_subst (P : Program) (σ : Subst) (t : Atom) :
    evalPlanned P (planOf t) (subst σ t) = evalIn P σ t := by
  match t with
  | .var v => simp [planOf, evalPlanned, subst, evalIn]
  | .symbol _ => simp [planOf, evalPlanned, subst, evalIn]
  | .grounded _ => simp [planOf, evalPlanned, subst, evalIn]
  | .expression es =>
    simp only [planOf, subst, evalPlanned, evalIn]
    rw [list es (fun a _ => evalPlanned_planOf_subst P σ a)]
termination_by sizeOf t
where
  list (as : List Atom)
      (ih : ∀ a ∈ as, evalPlanned P (planOf a) (subst σ a) = evalIn P σ a) :
      evalPlanned.evalPlannedList P (planOf.planOfList as)
          (subst.substList σ as) =
        evalIn.evalList P σ as := by
    induction as with
    | nil => rfl
    | cons first rest restHypothesis =>
      simp only [planOf.planOfList, subst.substList,
        evalPlanned.evalPlannedList, evalIn.evalList]
      rw [ih first (List.mem_cons_self ..),
        restHypothesis (fun b member => ih b (List.mem_cons_of_mem first member))]

/-! ## The planless reading -/

/-- A value is inert when evaluating it as code returns it unchanged. -/
def Inert (P : Program) (a : Atom) : Prop := evalCode P a = [a]

/-- When every substituted value is inert, evaluating the substituted term as
code is evaluation in the environment. -/
theorem evalCode_subst_of_inert (P : Program) (σ : Subst)
    (inert : ∀ v a, σ v = some a → Inert P a) (t : Atom) :
    evalCode P (subst σ t) = evalIn P σ t := by
  match t with
  | .var v =>
    cases bound : σ v with
    | none => simp [subst, evalIn, bound, SubstitutionAlgebra.empty]
    | some a =>
      have := inert v a bound
      simp only [Inert] at this
      simp [subst, evalIn, bound, this]
  | .symbol _ => simp [subst, evalIn]
  | .grounded _ => simp [subst, evalIn]
  | .expression es =>
    simp only [subst, evalIn]
    rw [list es (fun a _ => evalCode_subst_of_inert P σ inert a)]
termination_by sizeOf t
where
  list (as : List Atom)
      (ih : ∀ a ∈ as,
        evalIn P SubstitutionAlgebra.empty (subst σ a) = evalIn P σ a) :
      evalIn.evalList P SubstitutionAlgebra.empty (subst.substList σ as) =
        evalIn.evalList P σ as := by
    induction as with
    | nil => rfl
    | cons first rest restHypothesis =>
      simp only [subst.substList, evalIn.evalList]
      rw [ih first (List.mem_cons_self ..),
        restHypothesis (fun b member => ih b (List.mem_cons_of_mem first member))]

/-- One answer per child, each the child itself, is one choice: the children. -/
theorem choices_singletons (items : List Atom) :
    choices (items.map fun a => [a]) = [items] := by
  induction items with
  | nil => rfl
  | cons first rest restHypothesis =>
    simp [choices, restHypothesis]

/-- Children that are each inert evaluate, as code, each to itself. -/
theorem evalList_of_inert {P : Program} (items : List Atom)
    (inert : ∀ a ∈ items, Inert P a) :
    evalIn.evalList P SubstitutionAlgebra.empty items =
      items.map fun a => [a] := by
  induction items with
  | nil => rfl
  | cons first rest restHypothesis =>
    have head : evalIn P SubstitutionAlgebra.empty first = [first] :=
      inert first (List.mem_cons_self ..)
    simp only [evalIn.evalList, List.map_cons]
    rw [head, restHypothesis (fun b member => inert b
      (List.mem_cons_of_mem first member))]

/-- A value none of whose expressions the program calls. -/
inductive DataOnly (P : Program) : Atom → Prop
  | symbol (s : String) : DataOnly P (.symbol s)
  | grounded (g : GroundedValue) : DataOnly P (.grounded g)
  | var (v : String) : DataOnly P (.var v)
  | expression (es : List Atom) (children : ∀ a ∈ es, DataOnly P a)
      (notCall : P.isCall es = false) : DataOnly P (.expression es)

/-- A value none of whose expressions the program calls is inert. -/
theorem DataOnly.inert {P : Program} {a : Atom} (data : DataOnly P a) :
    Inert P a := by
  induction data with
  | symbol => rfl
  | grounded => rfl
  | var => rfl
  | expression es _ notCall childHypothesis =>
    simp only [Inert, evalIn, evalList_of_inert es childHypothesis,
      choices_singletons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, finish, notCall]
    simp

/-! ## Opening a binder with a fresh variable

A machine that applies `(|-> ($x) body)` to a value may substitute the value
for `$x`, which needs the body's plan (`evalPlanned_planOf_subst`), or rename
`$x` to a fresh variable and bind that variable to the value in the
environment, which needs no plan.  `evalIn_open_fresh` proves the second exact:
it is evaluation of the body with `$x` itself bound to the value. -/

/-- Evaluation in an environment reads the environment only at the term's own
variables. -/
theorem evalIn_congr_on_vars (P : Program) (σ τ : Subst) (t : Atom)
    (same : ∀ v ∈ SubstitutionAlgebra.vars t, σ v = τ v) :
    evalIn P σ t = evalIn P τ t := by
  match t with
  | .var v => simp [evalIn, same v (by simp [SubstitutionAlgebra.vars])]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es =>
    simp only [evalIn]
    rw [list es (fun a _ agree => evalIn_congr_on_vars P σ τ a agree)
      (by simpa [SubstitutionAlgebra.vars] using same)]
termination_by sizeOf t
where
  list (as : List Atom)
      (ih : ∀ a ∈ as, (∀ v ∈ SubstitutionAlgebra.vars a, σ v = τ v) →
        evalIn P σ a = evalIn P τ a)
      (same : ∀ v ∈ SubstitutionAlgebra.vars.varsList as, σ v = τ v) :
      evalIn.evalList P σ as = evalIn.evalList P τ as := by
    induction as with
    | nil => rfl
    | cons first rest restHypothesis =>
      have sameFirst : ∀ v ∈ SubstitutionAlgebra.vars first, σ v = τ v :=
        fun v member => same v (by simp [SubstitutionAlgebra.vars.varsList, member])
      have sameRest :
          ∀ v ∈ SubstitutionAlgebra.vars.varsList rest, σ v = τ v :=
        fun v member => same v (by simp [SubstitutionAlgebra.vars.varsList, member])
      simp only [evalIn.evalList]
      rw [ih first (List.mem_cons_self ..) sameFirst,
        restHypothesis (fun b member => ih b (List.mem_cons_of_mem first member))
          sameRest]

/-- A renaming binds variables only to variables. -/
def IsRenaming (τ : Subst) : Prop := ∀ v a, τ v = some a → ∃ w, a = .var w

/-- Evaluating a renamed term in an environment is evaluating the original
term in the environment read through the renaming. -/
theorem evalIn_subst_of_renaming (P : Program) (σ τ : Subst)
    (isRenaming : IsRenaming τ) (t : Atom) :
    evalIn P σ (subst τ t) =
      evalIn P (SubstitutionAlgebra.comp τ σ) t := by
  match t with
  | .var v =>
    cases bound : τ v with
    | none => simp [subst, evalIn, SubstitutionAlgebra.comp, bound]
    | some a =>
      obtain ⟨w, rfl⟩ := isRenaming v a bound
      simp [subst, evalIn, SubstitutionAlgebra.comp, bound]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es =>
    simp only [subst, evalIn]
    rw [list es (fun a _ => evalIn_subst_of_renaming P σ τ isRenaming a)]
termination_by sizeOf t
where
  list (as : List Atom)
      (ih : ∀ a ∈ as, evalIn P σ (subst τ a) =
        evalIn P (SubstitutionAlgebra.comp τ σ) a) :
      evalIn.evalList P σ (subst.substList τ as) =
        evalIn.evalList P (SubstitutionAlgebra.comp τ σ) as := by
    induction as with
    | nil => rfl
    | cons first rest restHypothesis =>
      simp only [subst.substList, evalIn.evalList]
      rw [ih first (List.mem_cons_self ..),
        restHypothesis (fun b member => ih b (List.mem_cons_of_mem first member))]

/-- The environment with one more variable bound. -/
def bindAt (σ : Subst) (x : SubstitutionAlgebra.Var) (a : Atom) : Subst :=
  fun v => if v = x then some a else σ v

/-- The renaming of one variable to another. -/
def renameTo (x y : SubstitutionAlgebra.Var) : Subst :=
  fun v => if v = x then some (.var y) else none

theorem renameTo_isRenaming (x y : SubstitutionAlgebra.Var) :
    IsRenaming (renameTo x y) := by
  intro v a bound
  by_cases same : v = x
  · simp only [renameTo, same, if_true, Option.some.injEq] at bound
    exact ⟨y, bound.symm⟩
  · simp [renameTo, same] at bound

/-- Opening a binder with a fresh variable bound to the argument is binding
the parameter itself. -/
theorem evalIn_open_fresh (P : Program) (σ : Subst)
    (x y : SubstitutionAlgebra.Var) (a body : Atom)
    (fresh : y ∉ SubstitutionAlgebra.vars body) :
    evalIn P (bindAt σ y a) (subst (renameTo x y) body) =
      evalIn P (bindAt σ x a) body := by
  rw [evalIn_subst_of_renaming P _ _ (renameTo_isRenaming x y) body]
  apply evalIn_congr_on_vars
  intro v member
  by_cases isParameter : v = x
  · subst isParameter
    simp [SubstitutionAlgebra.comp, renameTo, bindAt, subst]
  · have notFresh : v ≠ y := fun same => fresh (same ▸ member)
    simp [SubstitutionAlgebra.comp, renameTo, bindAt, isParameter, notFresh]

/-! ## Examples -/

namespace Examples

/-- A program whose one function, of no arguments, answers `42`: every
singleton expression holding a symbol is a call of it. -/
def callsSymbols : Program where
  isCall
    | [.symbol _] => true
    | _ => false
  answers _ := [.grounded (.int 42)]

/-- The syntax `($x)`. -/
def wrapVariable : Atom := .expression [.var "x"]

/-- `$x` bound to the value `(foo)`, which spells a call. -/
def boundToCall : Subst := fun _ => some (.expression [.symbol "foo"])

/-- `$x` bound to the number `1`. -/
def boundToNumber : Subst := fun _ => some (.grounded (.int 1))

/-- In the environment, `($x)` is the list holding the value `(foo)`. -/
theorem wrapVariable_in_environment :
    evalIn callsSymbols boundToCall wrapVariable =
      [.expression [.expression [.symbol "foo"]]] := by
  simp [evalIn, evalIn.evalList, wrapVariable, boundToCall, choices, finish,
    callsSymbols]

/-- Substituted and evaluated as code, the value `(foo)` is called again. -/
theorem wrapVariable_substituted_as_code :
    evalCode callsSymbols (subst boundToCall wrapVariable) =
      [.expression [.grounded (.int 42)]] := by
  simp [evalIn, evalIn.evalList, wrapVariable, boundToCall, choices, finish,
    callsSymbols, subst, subst.substList]

/-- The planless reading is not evaluation in the environment. -/
theorem evalCode_subst_evaluates_again :
    evalCode callsSymbols (subst boundToCall wrapVariable) ≠
      evalIn callsSymbols boundToCall wrapVariable := by
  rw [wrapVariable_substituted_as_code, wrapVariable_in_environment]
  simp

/-- Under the syntax's own plan, the substituted value stays a value. -/
theorem wrapVariable_planned :
    evalPlanned callsSymbols (planOf wrapVariable)
        (subst boundToCall wrapVariable) =
      [.expression [.expression [.symbol "foo"]]] := by
  rw [evalPlanned_planOf_subst, wrapVariable_in_environment]

/-- A number is inert, so for it the planless reading happens to agree. -/
theorem wrapVariable_number_as_code :
    evalCode callsSymbols (subst boundToNumber wrapVariable) =
      evalIn callsSymbols boundToNumber wrapVariable :=
  evalCode_subst_of_inert callsSymbols boundToNumber
    (fun _ a bound => by
      simp only [boundToNumber, Option.some.injEq] at bound
      subst bound
      exact (DataOnly.grounded (.int 1)).inert)
    wrapVariable

/-- The value `(foo)` is not inert: the program calls it. -/
theorem call_value_not_inert :
    ¬ Inert callsSymbols (.expression [.symbol "foo"]) := by
  simp [Inert, evalIn, evalIn.evalList, choices, finish, callsSymbols]

/-- Applying `(|-> ($x) ($x))` to `(foo)` by renaming `$x` to the fresh `$x'`
and binding `$x'`: the value stays a value. -/
theorem open_fresh_keeps_value :
    evalIn callsSymbols
        (bindAt SubstitutionAlgebra.empty "x'" (.expression [.symbol "foo"]))
        (subst (renameTo "x" "x'") wrapVariable) =
      [.expression [.expression [.symbol "foo"]]] := by
  rw [evalIn_open_fresh _ _ _ _ _ _ (by decide)]
  rfl

/-- The syntax `($x $y)`, whose `$y` is free. -/
def freeSecond : Atom := .expression [.var "x", .var "y"]

/-- An environment in which the free `$y` is `7`. -/
def yIsSeven : Subst := bindAt SubstitutionAlgebra.empty "y" (.grounded (.int 7))

/-- Freshness matters: renaming `$x` to the free `$y` captures it, and both
occurrences read the argument. -/
theorem open_captured_differs :
    evalIn callsSymbols (bindAt yIsSeven "y" (.grounded (.int 1)))
        (subst (renameTo "x" "y") freeSecond) ≠
      evalIn callsSymbols (bindAt yIsSeven "x" (.grounded (.int 1)))
        freeSecond := by
  decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
