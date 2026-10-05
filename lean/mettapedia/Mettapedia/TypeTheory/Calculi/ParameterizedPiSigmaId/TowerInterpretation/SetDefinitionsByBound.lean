import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion
import Mettapedia.Logic.HOL.Embedding.ZFSetInductiveRecursion

/-!
# A definition by equations whose calls go down a bound has a set model

A definition by equations need not call itself at a part of its argument: `log2 (suc (suc n))`
calls `log2` at the half of `suc (suc n)`, which is no part of it. Such a definition still has
a meaning when a **bound** goes down at every call: a map from the arguments into a set with a
well-founded relation `below`. For an inductive type `below` is its strict structural order; on
the numbers it is `∈` between numerals (`natBefore`).

**The theorem** (`definition_setModel_of_bound`). The package before the definition has a set
model at every assignment that agrees with a base one on its names, the defined name `f` is new
to it, and the declared type of `f` denotes the functions from a set `D` to a set `C`. Each
equation is read (`BoundReading`): its left side applies `f` to one argument, the pattern; its
right side is a body with the calls of `f` put in for the body's first variables; the pattern,
the arguments of the calls, the body and the telescope mention only names declared before. If
at every typed instance, an environment of an equation's telescope,
* the pattern lies in `D`, the right side lies in `C` whatever function from `D` to `C` the
  name denotes, and two instances with one argument are one instance (`BoundChecks`), and
* the argument of each call lies in `D` and its bound is below the bound of the pattern
  (`BoundObligations`),
then a value satisfies the equations (`bound_value`), so the package with the definition has a
set model, by `definition_setModel_of_value`. When the patterns also cover `D`
(`BoundCovers`), every set model gives `f` one and the same value (`bound_model_unique`). A set
model of a package with a definition satisfies its equations at every environment of their
telescopes (`definition_valid_of_setModel`), so a definition whose equations have no solution
has no model.

**What an admission check by a bound verifies, and the hypothesis each check provides.**
* The bound is typed from the arguments into an inductive type: `bound` with `into`. The strict
  structural order of an inductive type is well-founded: `wf`.
* The left sides are linear constructor patterns and no two overlap. Constructors are injective
  with disjoint ranges in the model, so this gives `BoundChecks.apart`.
* Both sides of each equation are typed, with `f` at its declared type and no rule of its own.
  By soundness this gives `BoundChecks.left_mem`, `BoundChecks.right_mem`, and the first half of
  each obligation: the argument of a call lies in `D`. Finding the calls in a right side is
  the reading as a body with calls; `f` occurs nowhere else in it.
* Each obligation, that the bound of a call's argument is below the bound of the left side's
  argument, proved in the judgment for all pattern variables. By soundness this gives the second
  half of `BoundObligations` at every typed instance.
* Patterns that cover every argument: `BoundCovers`, used only for uniqueness.
One hypothesis is not among the checks: the declared type has some value (`filler`). Without
it the right sides could lie in `C` only because no function from `D` to `C` exists. For
functions from numbers to numbers it holds.

**A declared datatype supplies the three semantic hypotheses.** Its structural order places
each recursive field's value before the constructor's value and continues down those fields,
and that order is well-founded on the datatype's set (`structOrder_wf`,
`reading_structOrder_wf`). Linear constructor patterns whose spines do not unify are apart
(`apart_of_linear_patterns`); variable-free patterns are data terms (`spinesMatch_of_toSet`).
One pattern for each constructor, with a variable in every field, covers the datatype's set
(`boundCovers_of_one_level`). The length of a list of numbers is such a definition, with the
list itself as the bound, and the value is unique (`ListLength.length_setModel`,
`ListLength.length_unique`). A cons pattern and a cons-of-nil pattern share a value
(`ListLength.cons_nil_not_apart`), and cons alone misses the empty list
(`ListLength.cons_misses_nil`).

**What the theorem does not give.** That the written equations, read as rewrite rules, stop
when they run at open terms is a fact about running, apart from the solution in sets. The
conversion of the package with these equations as its rules is covered by neither.

Positive example: `half` and `log2` with the bound `n`, and `log2` with the successor left out
of its third equation, whose one value is the zero function
(`Trinity/Log2/AdmittedBySetSolution.lean` in the executable model of the candidate). Negative
examples there: `f n = suc (f n)` passes every check except the obligations and has no set
model, and `f n = f n` has more than one; no bound goes down at either call.

A definition whose looping call stands strictly inside constructors of its result type, each
entered at a recursive field, and whose arguments are an instance of the left side, has no set
model (`containsItself_no_setModel`): the value would descend forever in the structural order.
A call that stands in a field which is not recursive is outside that shape, and the equation
can have a solution (`closedField_equation_has_solution`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp tracePiSet)
open ZFSetWellFoundedRecursion (before boundBefore boundBefore_wf ReadsBefore cases_solution
  cases_solution_unique)

universe u

variable {Head : Type} {R : Rules Head}

/-! ## Equations read for a bound -/

/-- **An equation read for admission by a bound.** The left side applies the defined name to
one argument, the pattern. The right side is the body with the calls of the defined name put in
for the body's first variables; the remaining variables are the equation's. The pattern, the
arguments of the calls, the body and the telescope mention only names that the package before
the definition declares, so the defined name occurs in the right side only at the calls. -/
structure BoundReading (B : ChurchRules R) (f : DeclName) where
  equation : DefiningEquation Head
  pattern : CTm Head equation.arity
  calls : Nat
  call : Fin calls → CTm Head equation.arity
  body : CTm Head (calls + equation.arity)
  left_eq : equation.left = .app (.const f) pattern
  right_eq : equation.right = body.subst (Fin.append (fun j => .app (.const f) (call j)) CTm.var)
  pattern_declared : ∀ c ∈ termConsts pattern, B.constantType c ≠ none
  call_declared : ∀ j, ∀ c ∈ termConsts (call j), B.constantType c ≠ none
  body_declared : ∀ c ∈ termConsts body, B.constantType c ≠ none
  telescope_declared :
    ∀ i, ∀ c ∈ termConsts (equation.telescope.lookup i), B.constantType c ≠ none

variable {B : ChurchRules R} {f : DeclName} (heads : Head → ZFSet.{u})

namespace BoundReading

variable (q : BoundReading B f) {base consts : DeclName → ZFSet.{u}}
  (agrees : ∀ c, B.constantType c ≠ none → consts c = base c)
include agrees

/-- The pattern has one value at assignments that agree on the names declared before. -/
theorem ev_pattern (η : Env.{u} q.equation.arity) :
    ev heads consts q.pattern η = ev heads base q.pattern η :=
  ev_congr_consts heads consts q.pattern (fun c mem => agrees c (q.pattern_declared c mem)) η

/-- So does the telescope. -/
theorem sat_iff (η : Env.{u} q.equation.arity) :
    Sat heads consts q.equation.telescope η ↔ Sat heads base q.equation.telescope η :=
  forall_congr' fun i => by
    rw [ev_congr_consts heads consts _ (fun c mem => agrees c (q.telescope_declared i c mem)) η]

/-- The left side is the value of the defined name applied to the pattern. -/
theorem ev_left (η : Env.{u} q.equation.arity) :
    ev heads consts q.equation.left η = traceApp (consts f) (ev heads base q.pattern η) := by
  rw [q.left_eq]
  exact congrArg (traceApp (consts f)) (q.ev_pattern heads agrees η)

/-- **The right side reads the defined name only at its calls**: it is the body at the values
of the defined name at the arguments of the calls. -/
theorem ev_right (η : Env.{u} q.equation.arity) :
    ev heads consts q.equation.right η =
      ev heads base q.body
        (Fin.append (fun j => traceApp (consts f) (ev heads base (q.call j) η)) η) := by
  rw [q.right_eq, ev_subst, ev_congr_consts heads consts q.body
    (fun c mem => agrees c (q.body_declared c mem))]
  congr 1
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · rw [Fin.append_left, Fin.append_left]
    exact congrArg (traceApp (consts f)) (ev_congr_consts heads consts (q.call j)
      (fun c mem => agrees c (q.call_declared j c mem)) η)
  · rw [Fin.append_right, Fin.append_right]
    rfl

end BoundReading

/-- An assignment changed at a name new to the package agrees with it on the names the package
declares. -/
theorem update_agrees_of_new (new : B.constantType f = none) (base : DeclName → ZFSet.{u})
    (F : ZFSet.{u}) : ∀ c, B.constantType c ≠ none → Function.update base f F c = base c :=
  fun c declared => Function.update_of_ne (fun same : c = f => declared (same ▸ new)) _ _

/-! ## What admission checks -/

/-- **The checks besides the obligations**, at every typed instance (an environment of an
equation's telescope at the base assignment): the pattern lies in `D`; the right side lies in `C`
whatever function from `D` to `C` the defined name denotes; and two instances whose patterns have
one value are one instance, so the left sides do not overlap. -/
structure BoundChecks (base : DeclName → ZFSet.{u}) (D C : ZFSet.{u})
    (eqs : List (BoundReading B f)) : Prop where
  left_mem : ∀ q ∈ eqs, ∀ η : Env.{u} q.equation.arity,
    Sat heads base q.equation.telescope η → ev heads base q.pattern η ∈ D
  right_mem : ∀ q ∈ eqs, ∀ η : Env.{u} q.equation.arity,
    Sat heads base q.equation.telescope η → ∀ F ∈ tracePiSet D (fun _ => C),
      ev heads (Function.update base f F) q.equation.right η ∈ C
  apart : ∀ q ∈ eqs, ∀ q' ∈ eqs,
    ∀ (η : Env.{u} q.equation.arity) (η' : Env.{u} q'.equation.arity),
    Sat heads base q.equation.telescope η → Sat heads base q'.equation.telescope η' →
    ev heads base q.pattern η = ev heads base q'.pattern η' →
    (⟨q, η⟩ : Σ q : BoundReading B f, Env.{u} q.equation.arity) = ⟨q', η'⟩

/-- **The obligations**, at every typed instance: the argument of each call lies in `D`, and its
bound is below the bound of the pattern. -/
def BoundObligations (base : DeclName → ZFSet.{u}) (D : ZFSet.{u})
    (below : ZFSet.{u} → ZFSet.{u} → Prop) (bound : ZFSet.{u} → ZFSet.{u})
    (eqs : List (BoundReading B f)) : Prop :=
  ∀ q ∈ eqs, ∀ η : Env.{u} q.equation.arity, Sat heads base q.equation.telescope η →
    ∀ j, before D (boundBefore below bound) (ev heads base (q.call j) η)
      (ev heads base q.pattern η)

/-- **The patterns cover the domain**: every member of `D` is the pattern of a typed
instance. -/
def BoundCovers (base : DeclName → ZFSet.{u}) (D : ZFSet.{u})
    (eqs : List (BoundReading B f)) : Prop :=
  ∀ x, x ∈ D → ∃ q ∈ eqs, ∃ η : Env.{u} q.equation.arity,
    Sat heads base q.equation.telescope η ∧ ev heads base q.pattern η = x

/-- A typed instance of the read equations. -/
private abbrev BoundInstance (base : DeclName → ZFSet.{u}) (eqs : List (BoundReading B f)) :=
  {p : Σ q : BoundReading B f, Env.{u} q.equation.arity //
    p.1 ∈ eqs ∧ Sat heads base p.1.equation.telescope p.2}

/-- The argument of a typed instance: the value of its pattern. -/
private noncomputable def instanceArg (base : DeclName → ZFSet.{u})
    (eqs : List (BoundReading B f)) (p : BoundInstance heads base eqs) : ZFSet.{u} :=
  ev heads base p.1.1.pattern p.1.2

/-- The right side of a typed instance, read on a value of the defined name. -/
private noncomputable def instanceRhs (base : DeclName → ZFSet.{u})
    (eqs : List (BoundReading B f)) (p : BoundInstance heads base eqs) (F : ZFSet.{u}) :
    ZFSet.{u} :=
  ev heads base p.1.1.body
    (Fin.append (fun j => traceApp F (ev heads base (p.1.1.call j) p.1.2)) p.1.2)

/-- With the obligations, each right side reads the defined name only below its argument. -/
private theorem reads_of_obligations {base : DeclName → ZFSet.{u}} {D : ZFSet.{u}}
    {below : ZFSet.{u} → ZFSet.{u} → Prop} {bound : ZFSet.{u} → ZFSet.{u}}
    {eqs : List (BoundReading B f)} (obligations : BoundObligations heads base D below bound eqs) :
    ReadsBefore (instanceArg heads base eqs) (instanceRhs heads base eqs) D
      (boundBefore below bound) := fun p _ _ same =>
  congrArg (fun φ => ev heads base p.1.1.body (Fin.append φ p.1.2))
    (funext fun j => same _ (obligations p.1.1 p.2.1 p.1.2 p.2.2 j))

/-! ## Existence -/

/-- **A value satisfies the equations.** Under the checks and the obligations, some function
from `D` to `C` satisfies every equation at every typed instance, at every assignment that
agrees with the base one on the names declared before and gives the defined name that
value. -/
theorem bound_value (new : B.constantType f = none) {base : DeclName → ZFSet.{u}}
    {eqs : List (BoundReading B f)} {D C T : ZFSet.{u}} {below : ZFSet.{u} → ZFSet.{u} → Prop}
    (wf : WellFounded (before T below)) {bound : ZFSet.{u} → ZFSet.{u}}
    (into : ∀ x, x ∈ D → bound x ∈ T) (checks : BoundChecks heads base D C eqs)
    (obligations : BoundObligations heads base D below bound eqs)
    {fallback : ZFSet.{u}} (filler : fallback ∈ tracePiSet D fun _ => C) :
    ∃ value ∈ tracePiSet D (fun _ => C), ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → consts f = value →
        ∀ e ∈ eqs.map BoundReading.equation, ∀ η : Env.{u} e.arity,
          Sat heads consts e.telescope η →
            ev heads consts e.left η = ev heads consts e.right η := by
  obtain ⟨value, mem, solves⟩ := cases_solution (instanceArg heads base eqs)
    (instanceRhs heads base eqs) (boundBefore_wf wf into)
    (fun p => checks.left_mem p.1.1 p.2.1 p.1.2 p.2.2)
    (fun p p' same _ => by
      obtain rfl : p = p' :=
        Subtype.ext (checks.apart p.1.1 p.2.1 p'.1.1 p'.2.1 p.1.2 p'.1.2 p.2.2 p'.2.2 same)
      rfl)
    (reads_of_obligations heads obligations)
    (fun p F hF => by
      have lands := checks.right_mem p.1.1 p.2.1 p.1.2 p.2.2 F hF
      rwa [p.1.1.ev_right heads (update_agrees_of_new new base F), Function.update_self] at lands)
    filler
  refine ⟨value, mem, fun consts agrees atValue e member η sat => ?_⟩
  obtain ⟨q, inEqs, rfl⟩ := List.mem_map.mp member
  rw [q.ev_left heads agrees, q.ev_right heads agrees, atValue]
  exact solves ⟨⟨q, η⟩, inEqs, (q.sat_iff heads agrees η).mp sat⟩

/-- **A definition by equations whose calls go down a bound has a set model.** The package
before the definition has a set model at every assignment that agrees with the base one on the
names it declares; the defined name is new to it; its declared type denotes the functions from
`D` to `C`; the equations pass the checks (`BoundChecks`) and their calls the obligations
(`BoundObligations`) for a bound into a set on which `below` is well-founded. Then for some
value of the defined name the package with the definition has a set model at every assignment
that agrees, on the names it declares, with the base assignment extended by the value. -/
theorem definition_setModel_of_bound (B : ChurchRules R) {base : DeclName → ZFSet.{u}}
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) {A : CTm Head 0} {eqs : List (BoundReading B f)}
    {D C T : ZFSet.{u}}
    (domain : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        ev heads consts A Fin.elim0 = tracePiSet D fun _ => C)
    {below : ZFSet.{u} → ZFSet.{u} → Prop} (wf : WellFounded (before T below))
    {bound : ZFSet.{u} → ZFSet.{u}} (into : ∀ x, x ∈ D → bound x ∈ T)
    (checks : BoundChecks heads base D C eqs)
    (obligations : BoundObligations heads base D below bound eqs)
    {fallback : ZFSet.{u}} (filler : fallback ∈ tracePiSet D fun _ => C) :
    ∃ value ∈ tracePiSet D (fun _ => C), ∀ consts : DeclName → ZFSet.{u},
      (∀ c, (withDefinition B f A (eqs.map BoundReading.equation)).constantType c ≠ none →
        consts c = Function.update base f value c) →
      SetModel heads consts (withDefinition B f A (eqs.map BoundReading.equation)) := by
  obtain ⟨value, mem, valid⟩ := bound_value heads new wf into checks obligations filler
  exact ⟨value, mem, definition_setModel_of_value B baseModel new value
    (fun consts agreesBase _ => (domain consts agreesBase).symm ▸ mem) valid⟩

/-! ## Uniqueness -/

/-- **A set model of a package with a definition satisfies its equations** at every environment
of their telescopes: the converse of `definition_setModel_of_value`. -/
theorem definition_valid_of_setModel {A : CTm Head 0} {eqs : List (DefiningEquation Head)}
    {consts : DeclName → ZFSet.{u}} (model : SetModel heads consts (withDefinition B f A eqs)) :
    ∀ e ∈ eqs, ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
      ev heads consts e.left η = ev heads consts e.right η := by
  intro e member η sat
  have equal := model.steps (Γ := e.telescope) (l := e.left.subst CTm.ids)
    (r := e.right.subst CTm.ids) (.inr ⟨e, member, CTm.ids, rfl, rfl⟩)
    (.inr ⟨⟨e, member, CTm.ids, rfl, rfl⟩, ⟨e, member, CTm.ids, rfl, rfl, rfl⟩⟩)
    (fun premise among => by
      obtain ⟨i, rfl⟩ := mem_telescopePremises.mp among
      intro ρ satρ
      show ρ i ∈ ev heads consts ((e.telescope.lookup i).subst CTm.ids) ρ
      rw [CTm.subst_ids]
      exact satρ i)
    η sat
  rwa [CTm.subst_ids, CTm.subst_ids] at equal

/-- **The value is unique when the patterns cover the domain.** Two set models of the package
with the definition, at assignments that agree with the base one on the names declared before,
give the defined name one value. Only the obligations and the cover are used. -/
theorem bound_model_unique (new : B.constantType f = none) {base : DeclName → ZFSet.{u}}
    {A : CTm Head 0} {eqs : List (BoundReading B f)} {D C T : ZFSet.{u}}
    (domain : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        ev heads consts A Fin.elim0 = tracePiSet D fun _ => C)
    {below : ZFSet.{u} → ZFSet.{u} → Prop} (wf : WellFounded (before T below))
    {bound : ZFSet.{u} → ZFSet.{u}} (into : ∀ x, x ∈ D → bound x ∈ T)
    (covers : BoundCovers heads base D eqs)
    (obligations : BoundObligations heads base D below bound eqs)
    {consts consts' : DeclName → ZFSet.{u}}
    (agrees : ∀ c, B.constantType c ≠ none → consts c = base c)
    (agrees' : ∀ c, B.constantType c ≠ none → consts' c = base c)
    (model : SetModel heads consts (withDefinition B f A (eqs.map BoundReading.equation)))
    (model' : SetModel heads consts' (withDefinition B f A (eqs.map BoundReading.equation))) :
    consts f = consts' f := by
  have solves : ∀ {κ : DeclName → ZFSet.{u}},
      (∀ c, B.constantType c ≠ none → κ c = base c) →
      SetModel heads κ (withDefinition B f A (eqs.map BoundReading.equation)) →
      κ f ∈ tracePiSet D (fun _ => C) ∧ ∀ p : BoundInstance heads base eqs,
        traceApp (κ f) (instanceArg heads base eqs p) = instanceRhs heads base eqs p (κ f) := by
    intro κ agreesκ modelκ
    refine ⟨?_, fun p => ?_⟩
    · have typed := modelκ.constants (withDefinition_defined B new)
      rwa [domain κ agreesκ] at typed
    · have equal := definition_valid_of_setModel heads modelκ p.1.1.equation
        (List.mem_map.mpr ⟨_, p.2.1, rfl⟩) p.1.2
        ((p.1.1.sat_iff heads agreesκ p.1.2).mpr p.2.2)
      rwa [p.1.1.ev_left heads agreesκ, p.1.1.ev_right heads agreesκ] at equal
  obtain ⟨mem, solvesF⟩ := solves agrees model
  obtain ⟨mem', solvesG⟩ := solves agrees' model'
  refine cases_solution_unique (instanceArg heads base eqs) (instanceRhs heads base eqs)
    (boundBefore_wf wf into) (fun x hx => ?_) (reads_of_obligations heads obligations)
    mem mem' solvesF solvesG
  obtain ⟨q, inEqs, η, sat, rfl⟩ := covers x hx
  exact ⟨⟨⟨q, η⟩, inEqs, sat⟩, rfl⟩

/-! ## A declared datatype supplies the three hypotheses -/

namespace DatatypeBound

open ZFSetInductive hiding Field
open ZFSetInductiveRecursion (SubPlus subPlus_wf subPlus_at subPlus_left_mem AtRecursive)
open Presentation.TypedEquality.Normalization (ctorTele)
open scoped ZFSet

local notation "DeclField" => TypedEquality.Normalization.Field

/-- The structural order of a datatype is well-founded on its carrier. -/
theorem structOrder_wf (sig : Signature.{u}) :
    WellFounded (before (carrier sig) (SubPlus sig)) :=
  Subrelation.wf (fun h => h.2) (subPlus_wf sig)

/-- Under a reading, that order is well-founded on the datatype's set. -/
theorem reading_structOrder_wf {consts : DeclName → ZFSet.{u}} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (DeclField Head))} {recN : DeclName}
    (reading : InductiveReading heads consts T v ctors recN) :
    WellFounded (before (consts T) (SubPlus (signature heads consts ctors))) := by
  rw [reading.type]
  exact structOrder_wf (signature heads consts ctors)

/-! ### A call inside its own value -/

/-- A term applied to arguments, the first argument first. -/
def applyTerms {n : Nat} (f : CTm Head n) : List (CTm Head n) → CTm Head n
  | [] => f
  | a :: as => applyTerms (.app f a) as

private theorem ev_applyTerms {consts : DeclName → ZFSet.{u}} {n : Nat} (f : CTm Head n) :
    ∀ (args : List (CTm Head n)) (η : Env.{u} n),
      ev heads consts (applyTerms f args) η =
        applyList (ev heads consts f η) (args.map fun a => ev heads consts a η)
  | [], _ => by rw [applyTerms, applyList, List.map_nil, List.foldl_nil]
  | a :: as, η => by
      rw [applyTerms, ev_applyTerms (.app f a) as, List.map_cons, applyList_cons]
      rfl

/-- A pattern instance, read as a substitution. A variable matches the term the substitution
gives it, so one variable matches one term wherever it occurs. An application matches
component by component. A constant matches itself. -/
inductive Inst {n : Nat} (σ : CSub Head n n) : CTm Head n → CTm Head n → Prop where
  | var (i : Fin n) : Inst σ (.var i) (σ i)
  | const (c : DeclName) : Inst σ (.const c) (.const c)
  | app {f a g b : CTm Head n} : Inst σ f g → Inst σ a b → Inst σ (.app f a) (.app g b)

private theorem ev_inst {consts : DeclName → ZFSet.{u}} {n : Nat} {σ : CSub Head n n}
    {pat arg : CTm Head n} (matched : Inst σ pat arg) (η : Env.{u} n) :
    ev heads consts pat (fun i => ev heads consts (σ i) η) = ev heads consts arg η := by
  induction matched with
  | var i => rfl
  | const c => rfl
  | app _ _ ihf iha =>
      change traceApp (ev heads consts _ _) (ev heads consts _ _) =
        traceApp (ev heads consts _ _) (ev heads consts _ _)
      rw [ihf, iha]

private theorem map_ev_inst {consts : DeclName → ZFSet.{u}} {n : Nat} {σ : CSub Head n n}
    {pats args : List (CTm Head n)} (matched : List.Forall₂ (Inst σ) pats args) (η : Env.{u} n) :
    pats.map (fun t => ev heads consts t (fun i => ev heads consts (σ i) η)) =
      args.map (fun t => ev heads consts t η) := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons, ev_inst heads head, ih]

/-- The value at a recursive field stands in `AtRecursive`. -/
private theorem atRecursive_get
    {fs : List ZFSetInductive.Field.{u}} {args : List ZFSet.{u}} {idx : Nat}
    (hidx : idx < fs.length) (hlen : args.length = fs.length)
    (rec : fs[idx]'hidx = ZFSetInductive.Field.recursive) :
    AtRecursive fs args (args[idx]'(hlen.symm ▸ hidx)) := by
  induction fs generalizing args idx with
  | nil => exact absurd hidx (Nat.not_lt_zero idx)
  | cons field fs ih =>
      cases args with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons _ args =>
          cases idx with
          | zero =>
              cases field with
              | recursive => exact AtRecursive.head
              | ofSet _ =>
                  simp only [List.getElem_cons_zero] at rec
                  cases rec
          | succ idx =>
              simp only [List.length_cons] at hidx hlen
              simp only [List.getElem_cons_succ] at rec
              exact AtRecursive.tail
                (ih (Nat.lt_of_succ_lt_succ hidx) (Nat.succ.inj hlen) rec)

/-- A call sits strictly inside constructors of a datatype, each entered at a recursive field.
The call at the root does not count: a bare call is not this shape, and a field that is not
recursive is not entered. -/
inductive InsideRecursive (ctors : List (DeclName × List (DeclField Head))) :
    {n : Nat} → CTm Head n → CTm Head n → Prop where
  | here {n : Nat} (i : Nat) (k : DeclName) (fields : List (DeclField Head))
      (args : List (CTm Head n)) (call : CTm Head n)
      (entry : ctors[i]? = some (k, fields)) (idx : Nat) (inRange : idx < fields.length)
      (count : args.length = fields.length) (recursive : fields[idx] = .recursive)
      (atArg : args[idx]'(count.symm ▸ inRange) = call) :
      InsideRecursive ctors call (applyTerms (.const k) args)
  | under {n : Nat} (i : Nat) (k : DeclName) (fields : List (DeclField Head))
      (args : List (CTm Head n)) (call field : CTm Head n)
      (entry : ctors[i]? = some (k, fields)) (idx : Nat) (inRange : idx < fields.length)
      (count : args.length = fields.length) (recursive : fields[idx] = .recursive)
      (atArg : args[idx]'(count.symm ▸ inRange) = field)
      (deeper : InsideRecursive ctors call field) :
      InsideRecursive ctors call (applyTerms (.const k) args)

/-- At an environment, each constructor entered by `InsideRecursive` is applied to arguments
that fit its fields. -/
inductive PathFits (consts : DeclName → ZFSet.{u}) (T : DeclName)
    (ctors : List (DeclName × List (DeclField Head))) :
    {n : Nat} → Env.{u} n → {call t : CTm Head n} → InsideRecursive ctors call t → Prop where
  | here {n : Nat} {η : Env.{u} n} {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
      {args : List (CTm Head n)} {call : CTm Head n}
      {entry : ctors[i]? = some (k, fields)} {idx : Nat} {inRange : idx < fields.length}
      {count : args.length = fields.length} {recursive : fields[idx] = .recursive}
      {atArg : args[idx]'(count.symm ▸ inRange) = call}
      (fits : Fits (consts T) (fields.map (fieldSig heads consts))
        (args.map fun a => ev heads consts a η)) :
      PathFits consts T ctors η
        (InsideRecursive.here i k fields args call entry idx inRange count recursive atArg)
  | under {n : Nat} {η : Env.{u} n} {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
      {args : List (CTm Head n)} {call field : CTm Head n}
      {entry : ctors[i]? = some (k, fields)} {idx : Nat} {inRange : idx < fields.length}
      {count : args.length = fields.length} {recursive : fields[idx] = .recursive}
      {atArg : args[idx]'(count.symm ▸ inRange) = field}
      {deeper : InsideRecursive ctors call field}
      (fits : Fits (consts T) (fields.map (fieldSig heads consts))
        (args.map fun a => ev heads consts a η))
      (inner : PathFits consts T ctors η deeper) :
      PathFits consts T ctors η
        (InsideRecursive.under i k fields args call field entry idx inRange count recursive
          atArg deeper)

/-- One constructor entered at a recursive field places that field's value strictly inside
the constructor's value. -/
private theorem subPlus_at_constructor
    {consts : DeclName → ZFSet.{u}} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (DeclField Head))} {recN : DeclName}
    (reading : InductiveReading heads consts T v ctors recN)
    {n : Nat} {η : Env.{u} n} {i : Nat} {k : DeclName}
    {fields : List (DeclField Head)} {args : List (CTm Head n)}
    (entry : ctors[i]? = some (k, fields))
    {idx : Nat} (inRange : idx < fields.length) (count : args.length = fields.length)
    (recursive : fields[idx]'inRange = .recursive)
    (fits : Fits (consts T) (fields.map (fieldSig heads consts))
      (args.map fun a => ev heads consts a η)) :
    SubPlus (signature heads consts ctors)
      (ev heads consts (args[idx]'(count.symm ▸ inRange)) η)
      (ev heads consts (applyTerms (.const k) args) η) := by
  set argVals : List ZFSet.{u} := args.map fun a => ev heads consts a η with argVals_eq
  have fitsCarrier : Fits (carrier (signature heads consts ctors))
      (fields.map (fieldSig heads consts)) argVals := by
    rw [argVals_eq, ← reading.type]
    exact fits
  have atSig := signature_getElem? heads consts entry
  have lenMap : (fields.map (fieldSig heads consts)).length = fields.length :=
    List.length_map (fieldSig heads consts)
  have idxMap : idx < (fields.map (fieldSig heads consts)).length := lenMap.symm ▸ inRange
  have recMapped :
      (fields.map (fieldSig heads consts))[idx]'idxMap = ZFSetInductive.Field.recursive := by
    rw [List.getElem_map (fieldSig heads consts), recursive, fieldSig]
  have lenArgs : argVals.length = (fields.map (fieldSig heads consts)).length := by
    rw [argVals_eq, List.length_map (fun a => ev heads consts a η), lenMap, count]
  have pos := atRecursive_get idxMap lenArgs recMapped
  have yEq : argVals[idx]'(lenArgs.symm ▸ idxMap) =
      ev heads consts (args[idx]'(count.symm ▸ inRange)) η := by
    change (args.map fun a => ev heads consts a η)[idx]'(by
      rw [← argVals_eq]
      exact lenArgs.symm ▸ idxMap) = _
    rw [List.getElem_map (fun a => ev heads consts a η)]
  have appEq : ev heads consts (applyTerms (.const k) args) η =
      constructorValue (nameCode k) argVals := by
    rw [ev_applyTerms heads]
    simpa [ev, argVals_eq] using ctor_apply (reading.ctor entry) fits
  have sub := subPlus_at atSig fitsCarrier pos
  rw [yEq] at sub
  rw [← appEq] at sub
  exact sub

private theorem subPlus_of_inside {consts : DeclName → ZFSet.{u}} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (DeclField Head))} {recN : DeclName}
    (reading : InductiveReading heads consts T v ctors recN) {n : Nat} {η : Env.{u} n}
    {call t : CTm Head n} {step : InsideRecursive ctors call t}
    (ok : PathFits heads consts T ctors η step) :
    SubPlus (signature heads consts ctors) (ev heads consts call η) (ev heads consts t η) := by
  induction ok with
  | @here _i _k _fields _args _call entry _idx inRange count recursive atArg fits =>
      have step :=
        subPlus_at_constructor heads reading entry inRange count recursive fits
      rw [atArg] at step
      exact step
  | @under _i _k _fields _args _call _field entry _idx inRange count recursive atArg
      _deeper fits _inner ih =>
      have stepField :=
        subPlus_at_constructor heads reading entry inRange count recursive fits
      rw [atArg] at stepField
      exact Relation.TransGen.trans ih stepField

/-- The arguments of the next environment are the values of a substitution. -/
noncomputable def nextEnv {consts : DeclName → ZFSet.{u}} {n : Nat} (σ : CSub Head n n)
    (η : Env.{u} n) : Env.{u} n :=
  fun i => ev heads consts (σ i) η

private def iterateEnv {n : Nat} (step : Env.{u} n → Env.{u} n) : Nat → Env.{u} n → Env.{u} n
  | 0, η => η
  | k + 1, η => step (iterateEnv step k η)

/-- The shape of a definition whose looping call stands inside its own value. The left side
applies the defined name to patterns. The call applies it to arguments that are an instance
of those patterns, by one substitution. The call stands strictly inside constructors of the
datatype, along recursive fields. -/
structure ContainsItself (ctors : List (DeclName × List (DeclField Head))) (fname : DeclName)
    (e : DefiningEquation Head) where
  σ : CSub Head e.arity e.arity
  pats : List (CTm Head e.arity)
  args : List (CTm Head e.arity)
  left_eq : e.left = applyTerms (.const fname) pats
  inside : InsideRecursive ctors (applyTerms (.const fname) args) e.right
  matched : List.Forall₂ (Inst σ) pats args

private theorem false_of_descending {α : Sort _} {r : α → α → Prop} (wf : WellFounded r)
    (seq : Nat → α) (desc : ∀ n, r (seq (n + 1)) (seq n)) : False := by
  suffices ∀ x, Acc r x → ∀ n, seq n = x → False by
    exact this (seq 0) (wf.apply (seq 0)) 0 rfl
  intro x acc
  induction acc with
  | intro x _ ih =>
      intro n rfl
      exact ih (seq (n + 1)) (desc n) (n + 1) rfl

private theorem ev_left_next {consts : DeclName → ZFSet.{u}} {fname : DeclName}
    {ctors : List (DeclName × List (DeclField Head))}
    {e : DefiningEquation Head} (shape : ContainsItself ctors fname e) (η : Env.{u} e.arity) :
    ev heads consts (applyTerms (.const fname) shape.args) η =
      ev heads consts e.left (nextEnv heads (consts := consts) shape.σ η) := by
  rw [shape.left_eq]
  rw [ev_applyTerms heads (consts := consts)]
  rw [ev_applyTerms heads (consts := consts)]
  unfold nextEnv
  exact congrArg (applyList (ev heads consts (.const fname) η))
    (map_ev_inst heads shape.matched η).symm

/-- **A definition whose looping call stands inside constructors along recursive fields has
no set model.** The call's arguments are an instance of the left side, so the equation
applies again at the next environment. Each such step places the next value strictly before
the current one in the structural order of the datatype, which is well-founded. The telescope
stays satisfied along those environments, and each constructor on the path is applied to
arguments that fit. -/
theorem containsItself_no_setModel {consts : DeclName → ZFSet.{u}} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (DeclField Head))} {recN : DeclName}
    (reading : InductiveReading heads consts T v ctors recN)
    {A : CTm Head 0} {eqs : List (DefiningEquation Head)} {e : DefiningEquation Head}
    {fname : DeclName} (model : SetModel heads consts (withDefinition B fname A eqs))
    (member : e ∈ eqs) (shape : ContainsItself ctors fname e) (η : Env.{u} e.arity)
    (sat : Sat heads consts e.telescope η)
    (stable : ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
      Sat heads consts e.telescope (nextEnv heads (consts := consts) shape.σ η))
    (fitting : ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
      PathFits heads consts T ctors η shape.inside) : False := by
  let seq : Nat → Env.{u} e.arity :=
    fun n => iterateEnv (nextEnv heads (consts := consts) shape.σ) n η
  have satIter : ∀ n, Sat heads consts e.telescope (seq n) := by
    intro n
    induction n with
    | zero => exact sat
    | succ n ih => exact stable (seq n) ih
  let val : Nat → ZFSet.{u} := fun n => ev heads consts e.left (seq n)
  have descend : ∀ n, before (consts T) (SubPlus (signature heads consts ctors))
      (val (n + 1)) (val n) := by
    intro n
    have equation := definition_valid_of_setModel heads model e member (seq n) (satIter n)
    have smaller := subPlus_of_inside heads reading (fitting (seq n) (satIter n))
    rw [ev_left_next heads shape (seq n), ← equation] at smaller
    exact ⟨by rw [reading.type]; exact subPlus_left_mem smaller, smaller⟩
  exact false_of_descending (reading_structOrder_wf heads reading) val descend

/-- An equation `x = C[observe x]` whose call stands in a closed field has a solution in the
carrier. The structural order does not enter that field, so the solution is not a descent. -/
theorem closedField_equation_has_solution (tag A a : ZFSet.{u}) (ha : a ∈ A)
    (observe : ZFSet.{u} → ZFSet.{u}) (ignores : ∀ x, observe x = a) :
    let sig : ZFSetInductive.Signature.{u} := [⟨tag, [.ofSet A]⟩]
    let x : ZFSet.{u} := constructorValue tag [a]
    x ∈ ZFSetInductive.carrier sig ∧ x = constructorValue tag [observe x] ∧
      ∀ y, ¬ ZFSetInductiveRecursion.Sub sig y x := by
  intro sig x
  refine ⟨?_, ?_, ?_⟩
  · have atIndex : (sig : List ZFSetInductive.Constructor.{u})[0]? =
        some ⟨tag, [.ofSet A]⟩ := rfl
    exact ZFSetInductive.constructor_mem_carrier atIndex (Fits.ofSet ha .nil)
  · rw [ignores]
  · intro y related
    obtain ⟨_, i, ctor, args, atIndex, _, _, pos⟩ := related
    have iZero : i = 0 := by
      cases i with
      | zero => rfl
      | succ j =>
          simp only [sig, List.getElem?_cons_succ, List.getElem?_nil] at atIndex
          cases atIndex
    cases iZero
    have ctorEq : ctor = ⟨tag, [.ofSet A]⟩ := by
      have spec : sig[0]? = some (⟨tag, [.ofSet A]⟩ : ZFSetInductive.Constructor.{u}) := by
        simp [sig]
      exact (Option.some.inj (spec.symm.trans atIndex)).symm
    have fieldsEq : ctor.fields = [.ofSet A] := by rw [ctorEq]
    have bad : AtRecursive [.ofSet A] args y := fieldsEq ▸ pos
    cases bad with
    | tail inner => cases inner

/-! ### Linear constructor patterns -/

/-- A constructor pattern: a variable, or a constructor applied to patterns. -/
inductive CPat where
  | var (i : Nat)
  | con (name : DeclName) (args : List CPat)

/-- The variable indices of a pattern, in order of occurrence. -/
def patVars : CPat → List Nat
  | .var i => [i]
  | .con _ args => args.flatMap patVars

/-- A pattern is linear when each variable occurs once. -/
def Linear (p : CPat) : Prop := (patVars p).Nodup

/-- Two patterns unify. A variable unifies with any pattern, and constructors unify when
they carry one name and corresponding arguments unify. -/
inductive SpinesMatch : CPat → CPat → Prop where
  | varLeft (i : Nat) (q : CPat) : SpinesMatch (.var i) q
  | varRight (p : CPat) (j : Nat) : SpinesMatch p (.var j)
  | con {k l : DeclName} {args args' : List CPat} (names : k = l)
      (argsMatch : List.Forall₂ SpinesMatch args args') :
      SpinesMatch (.con k args) (.con l args')

/-- The set of a pattern at an assignment of its variable indices. -/
noncomputable def patSet (ρ : Nat → ZFSet.{u}) : CPat → ZFSet.{u}
  | .var i => ρ i
  | .con k args => constructorValue (nameCode k) (args.map (patSet ρ))

private theorem linear_cons {k : DeclName} {a : CPat} {args : List CPat} :
    Linear (.con k (a :: args)) ↔
      Linear a ∧ Linear (.con k args) ∧
        ∀ i ∈ patVars a, ∀ j ∈ args.flatMap patVars, i ≠ j := by
  unfold Linear
  rw [patVars, List.flatMap_cons, patVars]
  exact List.nodup_append

private theorem linear_arg {k : DeclName} {args : List CPat} {a : CPat}
    (lin : Linear (.con k args)) (mem : a ∈ args) : Linear a := by
  induction args with
  | nil => cases mem
  | cons b args ih =>
      have parts := (linear_cons (k := k) (a := b)).mp lin
      cases mem with
      | head => exact parts.1
      | tail _ h => exact ih parts.2.1 h

private theorem mapped_eq {ρ ρ' : Nat → ZFSet.{u}} :
    ∀ {args : List CPat} {a : CPat},
      args.map (patSet ρ) = args.map (patSet ρ') → a ∈ args → patSet ρ a = patSet ρ' a
  | [], _, _, mem => nomatch mem
  | _ :: _, _, eq, mem => by
      rw [List.map_cons, List.map_cons] at eq
      injection eq with head tail
      cases mem with
      | head => exact head
      | tail _ h => exact mapped_eq tail h

private theorem pat_var_eq {ρ ρ' : Nat → ZFSet.{u}} :
    ∀ {p : CPat}, Linear p → patSet ρ p = patSet ρ' p → ∀ {i : Nat}, i ∈ patVars p → ρ i = ρ' i
  | .var _, _, eq, _, mem => by
      simp only [patVars, List.mem_singleton] at mem
      subst mem
      simpa [patSet] using eq
  | .con _ _, lin, eq, _, mem => by
      simp only [patSet] at eq
      obtain ⟨_, hargs⟩ := constructorValue_injective.mp eq
      rw [patVars] at mem
      obtain ⟨a, amem, imem⟩ := List.mem_flatMap.mp mem
      exact pat_var_eq (linear_arg lin amem) (mapped_eq hargs amem) imem

/-- The variables of an environment, and the empty set past its last index. -/
noncomputable def envFun {n : Nat} (η : Env.{u} n) : Nat → ZFSet.{u} :=
  fun i => if h : i < n then η ⟨i, h⟩ else ∅

private theorem envFun_fin {n : Nat} (η : Env.{u} n) (i : Fin n) : envFun η i.val = η i := by
  rw [envFun, dif_pos i.isLt]

private theorem env_determined {n : Nat} {η η' : Env.{u} n} {p : CPat} (lin : Linear p)
    (complete : ∀ i : Fin n, i.val ∈ patVars p)
    (eq : patSet (envFun η) p = patSet (envFun η') p) : η = η' := by
  funext i
  have h := pat_var_eq lin eq (complete i)
  rw [envFun_fin η i, envFun_fin η' i] at h
  exact h

mutual

private theorem spinesMatch_of_patSet {ρ ρ' : Nat → ZFSet.{u}} :
    (p q : CPat) → patSet ρ p = patSet ρ' q → SpinesMatch p q
  | .var i, q, _ => .varLeft i q
  | .con k args, .var j, _ => .varRight (.con k args) j
  | .con _ _, .con _ _, eq => by
      simp only [patSet] at eq
      obtain ⟨htag, hargs⟩ := constructorValue_injective.mp eq
      exact .con (nameCode_injective htag) (spinesMatch_of_patSet_list _ _ hargs)

private theorem spinesMatch_of_patSet_list {ρ ρ' : Nat → ZFSet.{u}} :
    (args args' : List CPat) → args.map (patSet ρ) = args'.map (patSet ρ') →
      List.Forall₂ SpinesMatch args args'
  | [], [], _ => .nil
  | [], _ :: _, eq => by
      rw [List.map_nil, List.map_cons] at eq
      exact nomatch eq
  | _ :: _, [], eq => by
      rw [List.map_cons, List.map_nil] at eq
      exact nomatch eq
  | _ :: _, _ :: _, eq => by
      rw [List.map_cons, List.map_cons] at eq
      injection eq with head tail
      exact .cons (spinesMatch_of_patSet _ _ head) (spinesMatch_of_patSet_list _ _ tail)

end

mutual

private theorem spinesMatch_self : (p : CPat) → SpinesMatch p p
  | .var i => .varLeft i (.var i)
  | .con _ args => .con rfl (spinesMatch_self_list args)

private theorem spinesMatch_self_list : (args : List CPat) → List.Forall₂ SpinesMatch args args
  | [] => .nil
  | a :: args => .cons (spinesMatch_self a) (spinesMatch_self_list args)

end

/-- A variable-free pattern, the constructor spine of a data term. -/
def ofData : DataTerm → CPat
  | .app name args => .con name (args.map ofData)

mutual

private theorem patSet_ofData : ∀ d : DataTerm,
    patSet (fun _ => (∅ : ZFSet.{u})) (ofData d) = d.toSet
  | .app name args => by
      rw [ofData, patSet, DataTerm.toSet_app_map]
      exact congrArg (constructorValue (nameCode name)) (patSet_ofData_list args)

private theorem patSet_ofData_list : ∀ ds : List DataTerm,
    (ds.map ofData).map (patSet (fun _ => (∅ : ZFSet.{u}))) = ds.map DataTerm.toSet
  | [] => rfl
  | d :: ds => by
      rw [List.map_cons, List.map_cons, List.map_cons, patSet_ofData d, patSet_ofData_list ds]

end

/-- Variable-free patterns with one set are one pattern. -/
theorem spinesMatch_of_toSet {d e : DataTerm} (same : d.toSet = e.toSet) :
    SpinesMatch (ofData d) (ofData e) := by
  obtain rfl := DataTerm.toSet_injective same
  exact spinesMatch_self (ofData d)

/-- A read equation whose pattern is a linear complete constructor pattern, rendered at the
base assignment. -/
structure PatReading (B : ChurchRules R) (f : DeclName) (base : DeclName → ZFSet.{u}) where
  reading : BoundReading B f
  pat : CPat
  linear : Linear pat
  complete : ∀ i : Fin reading.equation.arity, i.val ∈ patVars pat
  renders : ∀ η : Env.{u} reading.equation.arity,
    Sat heads base reading.equation.telescope η →
      ev heads base reading.pattern η = patSet (envFun η) pat

/-- Linear patterns that do not unify are apart: two typed instances with one pattern value
are one instance. -/
theorem apart_of_linear_patterns {base : DeclName → ZFSet.{u}}
    (items : List (PatReading heads B f base))
    (noOverlap : items.Pairwise fun a b =>
      ¬ SpinesMatch a.pat b.pat ∧ ¬ SpinesMatch b.pat a.pat) :
    ∀ q ∈ items.map (fun item => item.reading),
      ∀ q' ∈ items.map (fun item => item.reading),
        ∀ (η : Env.{u} q.equation.arity) (η' : Env.{u} q'.equation.arity),
          Sat heads base q.equation.telescope η →
            Sat heads base q'.equation.telescope η' →
              ev heads base q.pattern η = ev heads base q'.pattern η' →
                (⟨q, η⟩ : Σ q : BoundReading B f, Env.{u} q.equation.arity) = ⟨q', η'⟩ := by
  induction items with
  | nil =>
      intro q mem
      simp at mem
  | cons a items ih =>
      intro q qmem q' q'mem η η' sat sat' same
      have split := List.pairwise_cons.mp noOverlap
      simp only [List.map_cons, List.mem_cons] at qmem q'mem
      rcases qmem with rfl | qmem
      · rcases q'mem with rfl | q'mem
        · have eqPat := (a.renders η sat).symm.trans (same.trans (a.renders η' sat'))
          cases env_determined a.linear a.complete eqPat
          rfl
        · obtain ⟨b, bmem, rfl⟩ := List.mem_map.mp q'mem
          exact absurd (spinesMatch_of_patSet _ _ ((a.renders η sat).symm.trans
            (same.trans (b.renders η' sat')))) (split.1 b bmem).1
      · rcases q'mem with rfl | q'mem
        · obtain ⟨b, bmem, rfl⟩ := List.mem_map.mp qmem
          exact absurd (spinesMatch_of_patSet _ _ ((b.renders η sat).symm.trans
            (same.trans (a.renders η' sat')))) (split.1 b bmem).2
        · exact ih split.2 q qmem q' q'mem η η' sat sat' same

/-! ### One pattern for each constructor -/

/-- The constructor spine with a variable in each argument, the last variable newest. -/
def ctorSpine (k : DeclName) : (n : Nat) → CTm Head n
  | 0 => .const k
  | n + 1 => .app ((ctorSpine k n).rename wk) (.var 0)

private theorem ev_ctorSpine (consts : DeclName → ZFSet.{u}) (k : DeclName) :
    ∀ {n : Nat} (η : Env.{u} n),
      ev heads consts (ctorSpine k n) η = applyList (consts k) (envList η)
  | 0, _ => by
      rw [ctorSpine, ev, envList, applyList, List.foldl_nil]
  | n + 1, η => by
      rw [ctorSpine, ev, ev, ev_rename, ev_ctorSpine consts k (η ∘ wk)]
      have hlist : envList η = envList (η ∘ wk) ++ [η 0] := rfl
      rw [hlist, applyList_append, applyList_cons]
      simp only [applyList, List.foldl_nil]

/-- The one-level argument patterns `var (n - 1), …, var 0`. -/
def levelArgs : (n : Nat) → List CPat
  | 0 => []
  | n + 1 => .var n :: levelArgs n

/-- The one-level pattern of a constructor: the constructor at a variable in each field. -/
def levelPat (k : DeclName) (n : Nat) : CPat := .con k (levelArgs n)

private theorem levelArgs_indices :
    ∀ n, (levelArgs n).flatMap patVars = (List.range n).reverse
  | 0 => rfl
  | n + 1 => by
      rw [levelArgs, List.flatMap_cons, patVars, levelArgs_indices n, List.range_succ,
        List.reverse_append, List.reverse_singleton]

private theorem nodup_reverse_of {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
      rw [List.reverse_cons, List.nodup_append]
      refine ⟨ih (List.nodup_cons.mp h).2,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro same
      exact (List.nodup_cons.mp h).1 (same ▸ List.mem_reverse.mp hx)

private theorem levelPat_linear (k : DeclName) (n : Nat) : Linear (levelPat k n) := by
  unfold Linear levelPat
  rw [patVars, levelArgs_indices]
  exact nodup_reverse_of List.nodup_range

private theorem levelPat_complete (k : DeclName) (n : Nat) (i : Fin n) :
    i.val ∈ patVars (levelPat k n) := by
  rw [levelPat, patVars, levelArgs_indices, List.mem_reverse, List.mem_range]
  exact i.isLt

private theorem levelArgs_as_vars :
    ∀ n, levelArgs n = ((List.finRange n).reverse).map fun i => CPat.var i.val
  | 0 => by
      rw [levelArgs, List.finRange_zero, List.reverse_nil, List.map_nil]
  | n + 1 => by
      rw [levelArgs, levelArgs_as_vars n, List.finRange_succ_last, List.reverse_append,
        List.reverse_singleton, List.map_append, List.map_singleton, List.singleton_append]
      have hlast : CPat.var (Fin.last n).val = CPat.var n := congrArg CPat.var (Fin.val_last n)
      rw [hlast]
      apply congrArg (fun ts => CPat.var n :: ts)
      rw [List.map_reverse, List.map_reverse, List.map_map]
      apply congrArg List.reverse
      refine List.map_congr_left fun i _ => ?_
      exact (congrArg CPat.var (Fin.val_castSucc i)).symm

private theorem patSet_level (k : DeclName) {n : Nat} (η : Env.{u} n) :
    patSet (envFun η) (levelPat k n) = constructorValue (nameCode k) (envList η) := by
  rw [levelPat, patSet, levelArgs_as_vars, List.map_map]
  have hmap :
      ((List.finRange n).reverse).map (patSet (envFun η) ∘ fun i => CPat.var i.val) =
        ((List.finRange n).reverse).map η := by
    refine List.map_congr_left fun i _ => ?_
    show patSet (envFun η) (CPat.var i.val) = η i
    rw [patSet, envFun, dif_pos i.isLt]
  rw [hmap]
  exact congrArg (constructorValue (nameCode k)) (map_finRange_reverse η)

private theorem termConsts_rename {n m : Nat} (r : Ren n m) :
    ∀ t : CTm Head n, termConsts (t.rename r) = termConsts t
  | .var _ => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .pi A B => by
      rw [CTm.rename, termConsts, termConsts_rename r A, termConsts_rename (liftRen r) B, termConsts]
  | .sigma A B => by
      rw [CTm.rename, termConsts, termConsts_rename r A, termConsts_rename (liftRen r) B, termConsts]
  | .id A a b => by
      rw [CTm.rename, termConsts, termConsts_rename r A, termConsts_rename r a, termConsts_rename r b,
        termConsts]
  | .lam A b => by
      rw [CTm.rename, termConsts, termConsts_rename r A, termConsts_rename (liftRen r) b, termConsts]
  | .app f a => by
      rw [CTm.rename, termConsts, termConsts_rename r f, termConsts_rename r a, termConsts]
  | .pair a b => by
      rw [CTm.rename, termConsts, termConsts_rename r a, termConsts_rename r b, termConsts]
  | .fst p => by rw [CTm.rename, termConsts, termConsts_rename r p, termConsts]
  | .snd p => by rw [CTm.rename, termConsts, termConsts_rename r p, termConsts]
  | .refl a => by rw [CTm.rename, termConsts, termConsts_rename r a, termConsts]

private theorem termConsts_ctorSpine (k : DeclName) :
    ∀ n, termConsts (ctorSpine k n : CTm Head n) = [k]
  | 0 => rfl
  | n + 1 => by
      rw [ctorSpine, termConsts, termConsts_rename, termConsts_ctorSpine k n, termConsts,
        List.append_nil]

/-- An item covers one constructor when its telescope and its pattern are that constructor's,
one variable deep. -/
structure LevelMatch (T k : DeclName) (fields : List (DeclField Head))
    {base : DeclName → ZFSet.{u}} (item : PatReading heads B f base) : Prop where
  len : item.reading.equation.arity = fields.length
  tele : len ▸ item.reading.equation.telescope = liftCtx (ctorTele T fields)
  pat : item.pat = levelPat k fields.length

private theorem sat_cast (consts : DeclName → ZFSet.{u}) {n m : Nat} (h : n = m)
    (Γ : CCtx Head n) (Δ : CCtx Head m) (η : Env.{u} m) (hΓ : h ▸ Γ = Δ)
    (hs : Sat heads consts Δ η) : Sat heads consts Γ (h.symm ▸ η) := by
  cases h
  cases hΓ
  exact hs

private theorem envFun_cast {n m : Nat} (h : n = m) (η : Env.{u} m) :
    envFun (h.symm ▸ η) = envFun η := by
  cases h
  rfl

private theorem envList_cast {n m : Nat} (h : n = m) (η : Env.{u} m) :
    envList (h.symm ▸ η) = envList η := by
  cases h
  rfl

/-- One one-level pattern for each constructor covers the datatype's set. -/
theorem boundCovers_of_one_level {consts : DeclName → ZFSet.{u}} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (DeclField Head))} {recN : DeclName}
    (reading : InductiveReading heads consts T v ctors recN)
    {items : List (PatReading heads B f consts)}
    (covered : ∀ (i : Nat) (k : DeclName) (fields : List (DeclField Head)),
      ctors[i]? = some (k, fields) → ∃ item ∈ items, LevelMatch heads T k fields item) :
    BoundCovers heads consts (consts T) (items.map fun item => item.reading) := by
  intro x hx
  rw [reading.type] at hx
  obtain ⟨i, _c, args, atSig, fitting, valueEq⟩ := exists_inversion hx
  obtain ⟨k, fields, entry, hc⟩ := exists_of_signature_getElem? heads consts atSig
  cases hc
  obtain ⟨item, imem, match_⟩ := covered i k fields entry
  have fitsT : Fits (consts T) (fields.map (fieldSig heads consts)) args := by
    rw [reading.type]
    exact fitting
  have lengthEq : args.length = fields.length :=
    ((fits_iff heads consts fields args).mp fitsT).1
  let η₀ := envOf args fields.length
  have hsat₀ : Sat heads consts (liftCtx (ctorTele T fields)) η₀ :=
    (sat_ctorTele heads consts T fields args lengthEq).mpr fitsT
  let η : Env.{u} item.reading.equation.arity := match_.len.symm ▸ η₀
  have satη : Sat heads consts item.reading.equation.telescope η :=
    sat_cast heads consts match_.len item.reading.equation.telescope
      (liftCtx (ctorTele T fields)) η₀ match_.tele hsat₀
  have listed : envList η₀ = args := by
    rw [envList_envOf args fields.length (le_of_eq lengthEq.symm), ← lengthEq, List.take_length]
  have rendered := item.renders η satη
  rw [match_.pat, envFun_cast match_.len η₀, patSet_level, listed] at rendered
  exact ⟨item.reading, List.mem_map.mpr ⟨item, imem, rfl⟩, η, satη, rendered.trans valueEq⟩

/-! ### Length of a list of numbers -/

namespace ListLength

open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam)

/-- The name of the list type. -/
def listN : DeclName := .str .anonymous "list"

/-- The name of the empty list. -/
def nilN : DeclName := .str .anonymous "nil"

/-- The name of cons. -/
def consN : DeclName := .str .anonymous "cons"

/-- The name of the number type. -/
def numN : DeclName := .str .anonymous "num"

/-- The name of zero. -/
def zeroN : DeclName := .str .anonymous "zero"

/-- The name of successor. -/
def sucN : DeclName := .str .anonymous "suc"

/-- The name of length. -/
def lengthN : DeclName := .str .anonymous "length"

/-- The names a package declares before length. -/
def nameList : List DeclName := [listN, nilN, consN, numN, zeroN, sucN]

/-- The fields of cons: a number, then a list. -/
def listFields : List (DeclField Head) := [.closed (.const numN), .recursive]

/-- The constructors of lists of numbers. -/
def listCtors : List (DeclName × List (DeclField Head)) := [(nilN, []), (consN, listFields)]

private theorem nilEntry :
    (listCtors : List (DeclName × List (DeclField Head)))[0]? =
      some (nilN, ([] : List (DeclField Head))) := rfl

private theorem consEntry :
    (listCtors : List (DeclName × List (DeclField Head)))[1]? =
      some (consN, listFields) := rfl

/-- The declared type of length, from lists to numbers. -/
def lengthType : CTm Head 0 := .pi (.const listN) (.const numN)

/-- The telescope of cons. -/
def consTele : CCtx Head 2 := liftCtx (ctorTele listN listFields)

/-- What a package provides for length: a set model, a reading of the lists, and the numbers. -/
structure Setup where
  B : ChurchRules R
  base : DeclName → ZFSet.{u}
  baseModel : ∀ consts : DeclName → ZFSet.{u},
    (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B
  fresh : B.constantType lengthN = none
  declared : ∀ c ∈ nameList, B.constantType c ≠ none
  v : Head
  recN : DeclName
  reading : InductiveReading heads base listN v listCtors recN
  num : base numN = ZFSet.omega
  zero : base zeroN = numeral 0
  suc : ∀ n, n ∈ ZFSet.omega → traceApp (base sucN) n ∈ ZFSet.omega

variable (s : Setup (R := R) heads)

private theorem envList_two (η : Env.{u} 2) : envList η = [η 1, η 0] := by
  show envList (η ∘ Fin.succ) ++ [η 0] = [η 1, η 0]
  have htail : envList (η ∘ Fin.succ) = [η 1] := by
    show envList ((η ∘ Fin.succ) ∘ Fin.succ) ++ [(η ∘ Fin.succ) 0] = [η 1]
    rw [show envList ((η ∘ Fin.succ) ∘ Fin.succ) = ([] : List ZFSet.{u}) from rfl,
      List.nil_append]
    rfl
  rw [htail]
  rfl

private theorem nil_subst_eq :
    (CTm.const zeroN : CTm Head 0) =
      (CTm.const zeroN).subst
        (Fin.append (fun j : Fin 0 => CTm.app (CTm.const lengthN) (CTm.var (Fin.elim0 j)))
          (CTm.var : Fin 0 → CTm Head 0)) :=
  (CTm.subst_ids (CTm.const zeroN)).symm.trans
    (congrArg (fun σ => CTm.subst σ (CTm.const zeroN)) (funext fun i => i.elim0))

/-- The equation `length nil = zero`, with no call. -/
@[reducible] def nilReading : BoundReading s.B lengthN where
  equation := ⟨0, .nil, .app (.const lengthN) (.const nilN), .const zeroN⟩
  pattern := ctorSpine nilN 0
  calls := 0
  call := Fin.elim0
  body := .const zeroN
  left_eq := rfl
  right_eq := nil_subst_eq
  pattern_declared := by
    intro c mem
    rw [termConsts_ctorSpine] at mem
    simp at mem
    subst mem
    exact s.declared nilN (by simp [nameList])
  call_declared := fun j => j.elim0
  body_declared := by
    intro c mem
    simp [termConsts] at mem
    subst mem
    exact s.declared zeroN (by simp [nameList])
  telescope_declared := fun i => i.elim0

/-- The body of the cons equation, with the value of the call in the newest variable. -/
def consBody : CTm Head 3 := .app (.const sucN) (.var 0)

/-- The substitution that puts the call of length at the tail into that body. -/
def consSubst : CSub Head 3 2 :=
  Fin.append (fun _ : Fin 1 => CTm.app (CTm.const lengthN) (CTm.var (0 : Fin 2)))
    (CTm.var : Fin 2 → CTm Head 2)

/-- The equation `length (cons x l) = suc (length l)`. -/
@[reducible] def consReading : BoundReading s.B lengthN where
  equation := ⟨2, consTele, .app (.const lengthN) (ctorSpine consN 2), consBody.subst consSubst⟩
  pattern := ctorSpine consN 2
  calls := 1
  call := fun _ => .var 0
  body := consBody
  left_eq := rfl
  right_eq := rfl
  pattern_declared := by
    intro c mem
    rw [termConsts_ctorSpine] at mem
    simp at mem
    subst mem
    exact s.declared consN (by simp [nameList])
  call_declared := by
    intro _ c mem
    simp only [termConsts, List.mem_nil_iff] at mem
  body_declared := by
    intro c mem
    simp [consBody, termConsts] at mem
    subst mem
    exact s.declared sucN (by simp [nameList])
  telescope_declared := by
    intro i c mem
    match i with
    | ⟨0, _⟩ =>
        rw [show consTele.lookup ⟨0, by decide⟩ = .const listN from rfl] at mem
        simp [termConsts] at mem
        subst mem
        exact s.declared listN (by simp [nameList])
    | ⟨1, _⟩ =>
        rw [show consTele.lookup ⟨1, by decide⟩ = .const numN from rfl] at mem
        simp [termConsts] at mem
        subst mem
        exact s.declared numN (by simp [nameList])

private theorem cons_fits {η : Env.{u} 2} (sat : Sat heads s.base consTele η) :
    Fits (s.base listN) (listFields.map (fieldSig heads s.base)) (envList η) := by
  have satOf : Sat heads s.base consTele (envOf (envList η) 2) := by
    rw [envOf_envList]
    exact sat
  have lengthEq : (envList η).length = (listFields : List (DeclField Head)).length := by
    rw [envList_length]
    rfl
  exact (sat_ctorTele heads s.base listN (listFields : List (DeclField Head)) (envList η)
    lengthEq).mp satOf

private theorem cons_fields {η : Env.{u} 2} (sat : Sat heads s.base consTele η) :
    η 1 ∈ s.base numN ∧ η 0 ∈ s.base listN := by
  have fits := cons_fits heads s sat
  rw [envList_two η, listFields, List.map_cons, List.map_cons, List.map_nil, fieldSig, fieldSig]
    at fits
  cases fits with
  | ofSet headMem rest =>
      cases rest with
      | recursive tailMem _ =>
          rw [show ev heads s.base (liftTm (.const numN)) Fin.elim0 = s.base numN from rfl]
            at headMem
          exact ⟨headMem, tailMem⟩

private theorem cons_value {η : Env.{u} 2} (sat : Sat heads s.base consTele η) :
    ev heads s.base (ctorSpine consN 2) η =
      constructorValue (nameCode consN) (envList η) := by
  rw [ev_ctorSpine]
  exact ctor_apply (s.reading.ctor consEntry) (cons_fits heads s sat)

private theorem nil_value :
    ev heads s.base (ctorSpine nilN 0) (Fin.elim0 : Env.{u} 0) =
      constructorValue (nameCode nilN) [] := by
  rw [ev_ctorSpine, envList, applyList]
  exact s.reading.constant_value nilEntry

/-- The nil pattern, linear and complete, rendered by the reading. -/
@[reducible] def nilItem : PatReading heads s.B lengthN s.base where
  reading := (nilReading heads s)
  pat := levelPat nilN 0
  linear := levelPat_linear nilN 0
  complete := levelPat_complete nilN 0
  renders := by
    intro η _sat
    have : η = Fin.elim0 := by funext i; exact i.elim0
    cases this
    rw [show (nilReading heads s).pattern = ctorSpine nilN 0 from rfl, nil_value heads s, patSet_level, envList]

/-- The cons pattern, linear and complete, rendered by the reading. -/
@[reducible] def consItem : PatReading heads s.B lengthN s.base where
  reading := (consReading heads s)
  pat := levelPat consN 2
  linear := levelPat_linear consN 2
  complete := levelPat_complete consN 2
  renders := by
    intro η sat
    rw [show (consReading heads s).pattern = ctorSpine consN 2 from rfl, cons_value heads s sat, patSet_level]

private theorem items_readings :
    [(nilItem heads s), (consItem heads s)].map (fun item => item.reading) = [(nilReading heads s), (consReading heads s)] :=
  rfl

private theorem not_level_names {k l : DeclName} (h : k ≠ l) (n m : Nat) :
    ¬ SpinesMatch (levelPat k n) (levelPat l m) := by
  intro matched
  cases matched with
  | con names _ => exact h names

private theorem noOverlap :
    List.Pairwise (fun a b : PatReading heads s.B lengthN s.base =>
      ¬ SpinesMatch a.pat b.pat ∧ ¬ SpinesMatch b.pat a.pat) [(nilItem heads s), (consItem heads s)] := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨(fun _ mem => nomatch mem),
    List.Pairwise.nil⟩⟩
  intro b hb
  have hb' : b = (consItem heads s) := by simpa using hb
  cases hb'
  exact ⟨not_level_names (by decide : nilN ≠ consN) 0 2,
    not_level_names (by decide : consN ≠ nilN) 2 0⟩

private theorem nil_in_carrier : constructorValue (nameCode nilN) [] ∈ s.base listN := by
  rw [s.reading.type]
  exact constructor_mem_carrier (signature_getElem? heads s.base nilEntry) Fits.nil

private theorem cons_tail_below {η : Env.{u} 2} (sat : Sat heads s.base consTele η) :
    before (s.base listN)
      (boundBefore (SubPlus (signature heads s.base listCtors)) id) (η 0)
      (constructorValue (nameCode consN) [η 1, η 0]) := by
  obtain ⟨_, tailMem⟩ := cons_fields heads s sat
  unfold before boundBefore
  refine ⟨tailMem, ?_⟩
  dsimp [id]
  have fits := cons_fits heads s sat
  rw [envList_two η] at fits
  have fitsC : Fits (carrier (signature heads s.base listCtors))
      (listFields.map (fieldSig heads s.base)) [η 1, η 0] := s.reading.type ▸ fits
  have pos : AtRecursive (listFields.map (fieldSig heads s.base)) [η 1, η 0] (η 0) := by
    rw [listFields, List.map_cons, List.map_cons, List.map_nil, fieldSig, fieldSig]
    exact AtRecursive.tail AtRecursive.head
  exact subPlus_at (signature_getElem? heads s.base consEntry) fitsC pos

/-- The calls of length go down the list. -/
theorem length_obligations :
    BoundObligations heads s.base (s.base listN)
      (SubPlus (signature heads s.base listCtors)) id [(nilReading heads s), (consReading heads s)] := by
  intro q mem η sat j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact j.elim0
  · match j with
    | ⟨0, _⟩ =>
        have tail := cons_tail_below heads s sat
        have hcall : ev heads s.base ((consReading heads s).call ⟨0, Nat.zero_lt_one⟩) η = η 0 := rfl
        have hpat : ev heads s.base (consReading heads s).pattern η =
            constructorValue (nameCode consN) [η 1, η 0] := by
          rw [show (consReading heads s).pattern = ctorSpine consN 2 from rfl, cons_value heads s sat,
            envList_two η]
        rw [hcall, hpat]
        exact tail

private theorem nil_right {η : Env.{u} 0} {F : ZFSet.{u}} :
    ev heads (Function.update s.base lengthN F) (nilReading heads s).equation.right η ∈ ZFSet.omega := by
  have hr : (nilReading heads s).equation.right = .const zeroN := rfl
  rw [hr, ev, Function.update_of_ne (by decide : zeroN ≠ lengthN), s.zero]
  exact numeral_mem_omega 0

private theorem cons_right {η : Env.{u} 2} (sat : Sat heads s.base consTele η) {F : ZFSet.{u}}
    (hF : F ∈ tracePiSet (s.base listN) fun _ => ZFSet.omega) :
    ev heads (Function.update s.base lengthN F) (consReading heads s).equation.right η ∈
      ZFSet.omega := by
  have hr : (consReading heads s).equation.right = consBody.subst consSubst := rfl
  rw [hr, ev_subst]
  have h0 : consSubst (0 : Fin 3) =
      (CTm.app (CTm.const lengthN) (CTm.var (0 : Fin 2)) : CTm Head 2) := by
    have hz : (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) := Fin.ext rfl
    rw [consSubst, hz, Fin.append_left]
  have step : ev heads (Function.update s.base lengthN F) (consSubst (0 : Fin 3)) η =
      traceApp F (η 0) := by
    rw [h0]
    simp only [ev]
    rw [Function.update_self]
  rw [consBody]
  simp only [ev]
  rw [Function.update_of_ne (by decide : sucN ≠ lengthN), step]
  have tailMem := (cons_fields heads s sat).2
  exact s.suc _ (traceApp_mem_fibre hF tailMem)

/-- The two equations pass the checks. -/
theorem length_checks :
    BoundChecks heads s.base (s.base listN) ZFSet.omega [(nilReading heads s), (consReading heads s)] where
  left_mem := by
    intro q mem η sat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · have η0 : η = Fin.elim0 := by funext i; exact i.elim0
      cases η0
      rw [show (nilReading heads s).pattern = ctorSpine nilN 0 from rfl, nil_value heads s]
      exact nil_in_carrier heads s
    · rw [show (consReading heads s).pattern = ctorSpine consN 2 from rfl, cons_value heads s sat,
        s.reading.type]
      exact constructor_mem_carrier (signature_getElem? heads s.base consEntry)
        (s.reading.type ▸ cons_fits heads s sat)
  right_mem := by
    intro q mem η sat F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact nil_right heads s
    · exact cons_right heads s sat hF
  apart := by
    rw [← items_readings heads s]
    exact apart_of_linear_patterns heads [(nilItem heads s), (consItem heads s)] (noOverlap heads s)

private theorem length_domain {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, s.B.constantType c ≠ none → consts c = s.base c) :
    ev heads consts lengthType Fin.elim0 =
      tracePiSet (s.base listN) fun _ => ZFSet.omega := by
  rw [lengthType]
  simp only [ev]
  rw [agrees listN (s.declared listN (by simp [nameList])),
    agrees numN (s.declared numN (by simp [nameList])), s.num]

private theorem length_filler :
    traceLam (graph (s.base listN) fun _ => numeral 0) ∈
      tracePiSet (s.base listN) fun _ => ZFSet.omega :=
  traceLam_graph_mem fun _ _ => numeral_mem_omega 0

private theorem length_covers : BoundCovers heads s.base (s.base listN)
    [(nilReading heads s), (consReading heads s)] := by
  rw [← items_readings heads s]
  refine boundCovers_of_one_level heads s.reading ?_
  intro i k fields entry
  match i with
  | 0 =>
      have hk : k = nilN ∧ fields = [] := by
        have h : some (k, fields) = some (nilN, ([] : List (DeclField Head))) :=
          entry.symm.trans nilEntry
        exact Prod.mk.inj (Option.some.inj h)
      rcases hk with ⟨rfl, rfl⟩
      exact ⟨(nilItem heads s), List.mem_cons_self, ⟨rfl, rfl, rfl⟩⟩
  | 1 =>
      have hk : k = consN ∧ fields = listFields := by
        have h : some (k, fields) = some (consN, listFields) := entry.symm.trans consEntry
        exact Prod.mk.inj (Option.some.inj h)
      rcases hk with ⟨rfl, rfl⟩
      exact ⟨(consItem heads s), List.mem_cons_of_mem _ List.mem_cons_self, ⟨rfl, rfl, rfl⟩⟩
  | n + 2 =>
      have hlen : (listCtors : List (DeclName × List (DeclField Head))).length ≤ n + 2 := by
        rw [listCtors]
        exact Nat.le_add_left 2 n
      rw [List.getElem?_eq_none hlen] at entry
      exact nomatch entry

/-- Length, with the list itself as the bound, has a set model. The package is any one that
already reads the lists and the numbers. -/
theorem length_setModel : ∃ value ∈ tracePiSet (s.base listN) fun _ => ZFSet.omega,
    ∀ consts : DeclName → ZFSet.{u},
      (∀ c, (withDefinition s.B lengthN lengthType
        ([(nilReading heads s), (consReading heads s)].map BoundReading.equation)).constantType c ≠ none →
        consts c = Function.update s.base lengthN value c) →
      SetModel heads consts (withDefinition s.B lengthN lengthType
        ([(nilReading heads s), (consReading heads s)].map BoundReading.equation)) :=
  definition_setModel_of_bound (f := lengthN) heads s.B s.baseModel s.fresh
    (A := lengthType) (eqs := [(nilReading heads s), (consReading heads s)])
    (D := s.base listN) (C := ZFSet.omega) (T := s.base listN)
    (domain := fun _ agrees => length_domain heads s agrees)
    (below := SubPlus (signature heads s.base listCtors))
    (wf := reading_structOrder_wf heads s.reading)
    (bound := id) (into := fun _ hx => hx)
    (checks := length_checks heads s) (obligations := length_obligations heads s)
    (fallback := traceLam (graph (s.base listN) fun _ => numeral 0))
    (filler := length_filler heads s)

/-- The value of length is the same in every set model of the extended package. -/
theorem length_unique {consts consts' : DeclName → ZFSet.{u}}
    (agrees : ∀ c, s.B.constantType c ≠ none → consts c = s.base c)
    (agrees' : ∀ c, s.B.constantType c ≠ none → consts' c = s.base c)
    (model : SetModel heads consts (withDefinition s.B lengthN lengthType
      ([(nilReading heads s), (consReading heads s)].map BoundReading.equation)))
    (model' : SetModel heads consts' (withDefinition s.B lengthN lengthType
      ([(nilReading heads s), (consReading heads s)].map BoundReading.equation))) :
    consts lengthN = consts' lengthN :=
  bound_model_unique (f := lengthN) heads s.fresh
    (A := lengthType) (eqs := [(nilReading heads s), (consReading heads s)])
    (D := s.base listN) (C := ZFSet.omega) (T := s.base listN)
    (domain := fun _ ag => length_domain heads s ag)
    (below := SubPlus (signature heads s.base listCtors))
    (wf := reading_structOrder_wf heads s.reading)
    (bound := id) (into := fun _ hx => hx)
    (covers := length_covers heads s) (obligations := length_obligations heads s)
    agrees agrees' model model'

/-! ### Controls -/

/-- The pattern `cons x nil`, one variable deep in the number only. -/
def overlapPat : CPat := .con consN [.var 0, .con nilN []]

/-- The term `cons x nil`. -/
def overlapTerm : CTm Head 1 := .app (.app (.const consN) (.var 0)) (.const nilN)

/-- The equation `length (cons x nil) = zero`, overlapping the cons equation. -/
@[reducible] def overlapReading : BoundReading s.B lengthN where
  equation := ⟨1, .snoc .nil (.const numN), .app (.const lengthN) overlapTerm, .const zeroN⟩
  pattern := overlapTerm
  calls := 0
  call := Fin.elim0
  body := .const zeroN
  left_eq := rfl
  right_eq := rfl
  pattern_declared := by
    intro c mem
    simp [overlapTerm, termConsts] at mem
    rcases mem with rfl | rfl
    · exact s.declared consN (by simp [nameList])
    · exact s.declared nilN (by simp [nameList])
  call_declared := fun j => j.elim0
  body_declared := by
    intro c mem
    simp [termConsts] at mem
    subst mem
    exact s.declared zeroN (by simp [nameList])
  telescope_declared := by
    intro i c mem
    match i with
    | ⟨0, _⟩ =>
        rw [show ((.snoc .nil (.const numN) : CCtx Head 1).lookup ⟨0, by decide⟩) =
          .const numN from rfl] at mem
        simp [termConsts] at mem
        subst mem
        exact s.declared numN (by simp [nameList])

/-- The cons pattern and `cons x nil` unify. -/
theorem cons_nil_spines : SpinesMatch (levelPat consN 2) overlapPat := by
  rw [levelPat, levelArgs, overlapPat]
  exact .con rfl (.cons (.varLeft 1 (.var 0)) (.cons (.varLeft 0 (.con nilN [])) .nil))

private theorem nilSet_eq : s.base nilN = constructorValue (nameCode nilN) [] :=
  s.reading.constant_value nilEntry

private theorem overlap_fits :
    Fits (s.base listN) (listFields.map (fieldSig heads s.base))
      [numeral 0, constructorValue (nameCode nilN) []] := by
  rw [listFields, List.map_cons, List.map_cons, List.map_nil, fieldSig, fieldSig,
    show ev heads s.base (liftTm (.const numN)) Fin.elim0 = s.base numN from rfl, s.num]
  exact Fits.ofSet (numeral_mem_omega 0) (Fits.recursive (nil_in_carrier heads s) Fits.nil)

private noncomputable def overlap_env : Env.{u} 2 :=
  envOf [numeral 0, constructorValue (nameCode nilN) []] 2

private theorem overlap_sat : Sat heads s.base consTele (overlap_env) :=
  (sat_ctorTele heads s.base listN listFields
    [numeral 0, constructorValue (nameCode nilN) []] rfl).mpr (overlap_fits heads s)

private noncomputable def one_env : Env.{u} 1 := extend (Fin.elim0 : Env.{u} 0) (numeral 0)

private theorem one_sat : Sat heads s.base (.snoc .nil (.const numN)) (one_env) := by
  unfold one_env
  refine (sat_snoc heads s.base).mpr ⟨fun i => i.elim0, ?_⟩
  rw [ev, s.num]
  exact numeral_mem_omega 0

private theorem shared_value :
    ev heads s.base (consReading heads s).pattern (overlap_env) =
      ev heads s.base (overlapReading heads s).pattern (one_env) := by
  rw [show (consReading heads s).pattern = ctorSpine consN 2 from rfl, cons_value heads s (overlap_sat heads s)]
  have listed : envList (overlap_env) =
      [numeral 0, constructorValue (nameCode nilN) []] := by
    rw [overlap_env, envList_envOf _ 2 (Nat.le_refl _)]
    rfl
  rw [listed]
  rw [show (overlapReading heads s).pattern = overlapTerm from rfl, overlapTerm]
  simp only [ev, one_env, extend_zero]
  rw [← nilSet_eq heads s]
  have happ : applyList (s.base consN) [numeral 0, s.base nilN] =
      constructorValue (nameCode consN) [numeral 0, constructorValue (nameCode nilN) []] := by
    rw [nilSet_eq heads s]
    exact ctor_apply (s.reading.ctor consEntry) (overlap_fits heads s)
  have hlist : applyList (s.base consN) [numeral 0, s.base nilN] =
      traceApp (traceApp (s.base consN) (numeral 0)) (s.base nilN) := rfl
  rw [← hlist, happ, nilSet_eq heads s]

/-- `length (cons x l)` and `length (cons x nil)` share the value `cons 0 nil`. -/
theorem cons_nil_not_apart :
    ¬ ∀ q ∈ [(consReading heads s), (overlapReading heads s)],
        ∀ q' ∈ [(consReading heads s), (overlapReading heads s)],
          ∀ (η : Env.{u} q.equation.arity) (η' : Env.{u} q'.equation.arity),
            Sat heads s.base q.equation.telescope η →
              Sat heads s.base q'.equation.telescope η' →
                ev heads s.base q.pattern η = ev heads s.base q'.pattern η' →
                  (⟨q, η⟩ : Σ q : BoundReading s.B lengthN, Env.{u} q.equation.arity) =
                    ⟨q', η'⟩ := by
  intro apart
  have same := apart (consReading heads s) List.mem_cons_self (overlapReading heads s)
    (List.mem_cons_of_mem _ List.mem_cons_self) (overlap_env) (one_env)
    (overlap_sat heads s) (one_sat heads s) (shared_value heads s)
  have har : (consReading heads s).equation.arity = (overlapReading heads s).equation.arity :=
    congrArg (fun q : BoundReading s.B lengthN => q.equation.arity) (congrArg Sigma.fst same)
  change (2 : Nat) = 1 at har
  exact absurd har (by decide)

/-- Cons alone misses the empty list. -/
theorem cons_misses_nil : ¬ BoundCovers heads s.base (s.base listN) [(consReading heads s)] := by
  intro covers
  obtain ⟨q, mem, η, sat, eqv⟩ := covers _ (nil_in_carrier heads s)
  have hq : q = (consReading heads s) := by simpa using mem
  cases hq
  rw [show (consReading heads s).pattern = ctorSpine consN 2 from rfl, cons_value heads s sat] at eqv
  exact constructorValue_ne_of_tag_ne (nameCode_injective.ne (by decide : nilN ≠ consN))
    [] (envList η) eqv.symm

end ListLength

end DatatypeBound

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
