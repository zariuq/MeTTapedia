import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Norm

/-!
# Structurally descending deterministic equations

The loader of deterministic equation plans admits a program only when every
call its equations make descends.  This module states that criterion over the
program model of `Program`; `Termination` proves it sound: under an admitted
program, every call ends (`apply_terminates`).

A *function* is a head at an arity.  A *certificate* gives every function, at
each of a fixed list of levels, a set of argument positions and a potential.
At a measured position every equation of the function has a headed pattern.
The measure of a call at a level is the sum of the norms of its arguments at
the positions plus the potential, and the measures of a call are compared
lexicographically over the levels.

A call an equation makes, a *site*, is bounded from its syntax.  Each argument
at a position of the callee's set has a cost: a use of a variable of the
equation's patterns at the caller's positions costs 0 and uses the variable,
reached also through `let` binders that carry a variable or a norm-keeping view
of one; an atom and an atom-valued primitive cost 1; a value view and a
norm-keeping primitive cost their argument; a cell, a list value and any other
constructor cost their overhead plus their elements.  The uses of all the
arguments are distinct.  The *weight* of the site is the total cost minus the
overheads of the caller's patterns at its positions and the number of their
variables left unused.  At a level the site does not grow when the weight
plus the callee's potential minus the caller's is at most 0, and descends when
it is at most -1; the certificate is valid when every site does not grow at
each level before one where it descends.

The definitions follow the loader's check (the C function
`cetta_deterministic_equation_descends_v1`) step by step: the same head kinds,
the same order of claiming uses, the same weights and the same scan of
levels.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-! ## The vocabulary -/

/-- What the value of a primitive call is known to be. -/
inductive PrimitiveClass where
  /-- Not a primitive: the call is a constructor of its values. -/
  | none
  /-- An atom, of norm 1. -/
  | atom
  /-- One argument, and a value of norm at most the argument's. -/
  | preserving
  /-- A value no argument bounds. -/
  | structure
  deriving DecidableEq, Repr

/-- The class of each primitive head at an arity. -/
structure Vocabulary where
  classify : String → Nat → PrimitiveClass

/-- A host keeps a vocabulary's promises: exactly the classified heads are
handled, atom-valued ones give atoms, and norm-keeping ones take one argument
and give a value of norm at most its norm. -/
structure Keeps (V : Vocabulary) (H : Host) : Prop where
  unclassified : ∀ f vs, V.classify f vs.length = .none → H.primitive f vs = .unhandled
  handled : ∀ f vs, V.classify f vs.length ≠ .none → H.primitive f vs ≠ .unhandled
  atom : ∀ f vs v, V.classify f vs.length = .atom → H.primitive f vs = .value v →
    norm v = 1
  preserving : ∀ f vs v, V.classify f vs.length = .preserving →
    H.primitive f vs = .value v → ∃ u, vs = [u] ∧ norm v ≤ norm u

/-! ## Heads, views and binders -/

/-- What evaluation does with a symbol-headed call. -/
inductive HeadKind where
  | call | fails | atom | preserving | structure | cell | view | constructor
  deriving DecidableEq, Repr

/-- The evaluator's decision for a head at an arity: an equation of the
program, a failure for a head defined at other arities only, the vocabulary's
primitive, else a constructor, a cell or a value view by its head. -/
def headKind (P : Program) (V : Vocabulary) (f : String) (n : Nat) : HeadKind :=
  if P.definesAt f n then .call
  else if P.defines f then .fails
  else
    match V.classify f n with
    | .atom => .atom
    | .preserving => if n = 1 then .preserving else .structure
    | .structure => .structure
    | .none =>
      if n = 2 ∧ f = "LCons" then .cell
      else if n = 1 ∧ isView f = true then .view
      else .constructor

/-- The argument of a view that keeps its argument's norm: a value-view
constructor or a norm-keeping primitive of one argument. -/
def viewArgument (P : Program) (V : Vocabulary) : Term → Option Term
  | .expr [.sym f, x] =>
    match headKind P V f 1 with
    | .view => some x
    | .preserving => some x
    | _ => none
  | _ => none

theorem sizeOf_lt_of_viewArgument {P : Program} {V : Vocabulary} {t x : Term}
    (h : viewArgument P V t = some x) : sizeOf x < sizeOf t := by
  unfold viewArgument at h
  split at h
  · rename_i f y
    split at h <;> first
      | (cases h; simp; omega)
      | cases h
  · cases h

/-- A term with its norm-keeping views taken off. -/
def strip (P : Program) (V : Vocabulary) (t : Term) : Term :=
  match _h : viewArgument P V t with
  | some x => strip P V x
  | none => t
termination_by sizeOf t
decreasing_by exact sizeOf_lt_of_viewArgument _h

/-- A `let` binder in scope: the variable it carries, if any. -/
structure Binder where
  var : String
  carried : Option String

/-- The innermost binder of a variable. -/
def lookupBinder (env : List Binder) (x : String) : Option Binder :=
  env.find? (fun b => b.var == x)

/-- The variable a term carries through views, resolved through the binders
in scope, if any. -/
def carried (P : Program) (V : Vocabulary) (env : List Binder) (t : Term) :
    Option String :=
  match strip P V t with
  | .var x =>
    match lookupBinder env x with
    | some b => b.carried
    | none => some x
  | _ => none

/-! ## Sites -/

/-- A call an equation's right side makes: the callee, its argument terms
and the binders in scope. -/
structure Site where
  callee : String
  args : List Term
  env : List Binder

mutual

/-- Every call evaluation of a term can make: evaluation is call by value, so
every subterm is evaluated, the binder of a `let` and the argument of
`metta-nullary` excepted, and a `let`'s body sees its binder. -/
def sites (P : Program) (V : Vocabulary) (env : List Binder) : Term → List Site
  | .expr [] => []
  | .expr [.sym "let", b, e, body] =>
    sites P V env e ++
      (match b with
       | .var x => sites P V (⟨x, carried P V env e⟩ :: env) body
       | _ => [])
  | .expr [.sym "metta-nullary", _] => []
  | .expr (.sym f :: args) =>
    (if P.definesAt f args.length then [⟨f, args, env⟩] else []) ++
      sitesList P V env args
  | .expr items => sitesList P V env items
  | .list items => sitesList P V env items
  | _ => []

/-- The calls of a list of terms. -/
def sitesList (P : Program) (V : Vocabulary) (env : List Binder) :
    List Term → List Site
  | [] => []
  | t :: ts => sites P V env t ++ sitesList P V env ts

end

/-! ## Costs and weights -/

mutual

/-- The variables of a pattern, one per occurrence. -/
def patternVars : Term → List String
  | .var x => [x]
  | .expr items => patternVarsList items
  | .list items => patternVarsList items
  | _ => []

/-- The variables of a list of patterns, in order. -/
def patternVarsList : List Term → List String
  | [] => []
  | t :: ts => patternVars t ++ patternVarsList ts

end

/-- A variable of the patterns at the measured positions. -/
def measuredVar (params : List Term) (S : List Nat) (y : String) : Bool :=
  S.any (fun i => match params[i]? with
    | some p => (patternVars p).contains y
    | none => false)

mutual

/-- The cost of an argument: the norm its value may have beyond the norms of
the variables it uses, which are added to `uses`; `none` when it has no
bound. -/
def cost (P : Program) (V : Vocabulary) (params : List Term) (S : List Nat)
    (env : List Binder) : Term → List String → Option (Nat × List String)
  | .var x, uses =>
    let y := match lookupBinder env x with
      | some b => b.carried
      | none => some x
    match y with
    | some y =>
      if measuredVar params S y && !uses.contains y then some (0, y :: uses) else none
    | none => none
  | .sym _, uses => some (1, uses)
  | .lit _, uses => some (1, uses)
  | .list items, uses =>
    (costList P V params S env items uses).map
      (fun r => (1 + items.length + r.1, r.2))
  | .expr [], uses => some (1, uses)
  | .expr [.sym "let", _, _, _], _ => none
  | .expr [.sym "metta-nullary", .sym _], uses => some (3, uses)
  | .expr [.sym "metta-nullary", _], _ => none
  | .expr (.sym f :: args), uses =>
    match headKind P V f args.length, hargs : args with
    | .atom, _ => some (1, uses)
    | .preserving, [x] => cost P V params S env x uses
    | .view, [x] => cost P V params S env x uses
    | .cell, [h, t] =>
      match cost P V params S env h uses with
      | some (ch, u₁) =>
        match cost P V params S env t u₁ with
        | some (ct, u₂) => some (1 + ch + ct, u₂)
        | none => none
      | none => none
    | .constructor, _ =>
      (costList P V params S env args uses).map
        (fun r => (1 + (args.length + 1) + 1 + r.1, r.2))
    | _, _ => none
  | .expr items, uses =>
    (costList P V params S env items uses).map
      (fun r => (1 + items.length + r.1, r.2))
termination_by t => (sizeOf t, 1)
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | (subst hargs; simp_wf; omega)

/-- The costs of a list of arguments, from left to right. -/
def costList (P : Program) (V : Vocabulary) (params : List Term) (S : List Nat)
    (env : List Binder) : List Term → List String → Option (Nat × List String)
  | [], uses => some (0, uses)
  | t :: ts, uses =>
    match cost P V params S env t uses with
    | some (c, u₁) =>
      match costList P V params S env ts u₁ with
      | some (cs, u₂) => some (c + cs, u₂)
      | none => none
    | none => none
termination_by ts => (sizeOf ts, 0)

end

/-- The variables of a pattern no argument used. -/
def unused (p : Term) (uses : List String) : Nat :=
  ((patternVars p).filter (fun y => !uses.contains y)).length

/-- The costs of a site's arguments at the given positions, in order, added to
a total, each claiming its uses after the uses already claimed; `none` when
one has no bound. -/
def costAt (P : Program) (V : Vocabulary) (params : List Term) (Sf : List Nat)
    (site : Site) : List Nat → Nat → List String → Option (Nat × List String)
  | [], total, uses => some (total, uses)
  | j :: js, total, uses =>
    match cost P V params Sf site.env (site.args.getD j (.expr [])) uses with
    | some (c, uses') => costAt P V params Sf site js (total + c) uses'
    | none => none

/-- The overheads of the caller's patterns at its positions and the number of
their variables left unused. -/
def slack (params : List Term) (Sf : List Nat) (uses : List String) : Nat :=
  (((List.range params.length).filter (fun i => Sf.contains i)).map
    (fun i => overhead (params.getD i (.expr [])) + unused (params.getD i (.expr [])) uses)).sum

/-- The weight of a site under the caller's positions `Sf` and the callee's
`Sg`: arguments that are plain uses claim their variables first, the others
after, each group from left to right. -/
def weigh (P : Program) (V : Vocabulary) (params : List Term) (Sf Sg : List Nat)
    (site : Site) : Option Int :=
  let measured := (List.range site.args.length).filter (fun j => Sg.contains j)
  let plain := fun j => (carried P V site.env (site.args.getD j (.expr []))).isSome
  let order := measured.filter plain ++ measured.filter (fun j => !plain j)
  match costAt P V params Sf site order 0 [] with
  | some (total, uses) => some ((total : Int) - slack params Sf uses)
  | none => none

/-! ## Certificates -/

/-- The positions and potentials of every function at one level. -/
structure Level where
  set : String → Nat → List Nat
  potential : String → Nat → Nat

/-- A descent certificate: its levels, in order. -/
structure Certificate where
  levels : List Level

/-- Whether a site of an equation does not grow at each level before one where
it descends. -/
def decides (P : Program) (V : Vocabulary) (e : Equation) (site : Site) :
    List Level → Bool
  | [] => false
  | l :: ls =>
    match weigh P V e.params (l.set e.head e.params.length)
        (l.set site.callee site.args.length) site with
    | none => false
    | some w =>
      let b := w + (l.potential site.callee site.args.length : Int) -
        (l.potential e.head e.params.length : Int)
      if b ≤ -1 then true else if b ≤ 0 then decides P V e site ls else false

/-- Every measured position of a function holds a headed pattern in each of
its equations. -/
def Measured (P : Program) (c : Certificate) : Prop :=
  ∀ l ∈ c.levels, ∀ e ∈ P, ∀ i ∈ l.set e.head e.params.length,
    ∃ p, e.params[i]? = some p ∧ headed p = true

/-- No variable occurs twice in an equation's left side. -/
def LeftLinear (P : Program) : Prop :=
  ∀ e ∈ P, (patternVarsList e.params).Nodup

/-- A certificate shows a program descends: its positions are measured and
every site of every equation is decided. -/
def Descends (P : Program) (V : Vocabulary) (c : Certificate) : Prop :=
  LeftLinear P ∧ Measured P c ∧
    ∀ e ∈ P, ∀ s ∈ sites P V [] e.body, decides P V e s c.levels = true

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
