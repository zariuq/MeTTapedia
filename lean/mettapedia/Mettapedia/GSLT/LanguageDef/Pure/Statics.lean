/-
# Pure dependent spine statics

This is the small dependent fragment used by the typed-hole root.  It has one
unlevelled sort, de Bruijn variables, Pi, lambda, and application.  There is no
constant namespace, universe hierarchy, conversion rule, or reduction rule.
External binder names are interned separately; the trusted syntax below uses
only natural-number indices.
-/

import Mathlib.Tactic

namespace Mettapedia.GSLT.LanguageDef.Pure

/-- The unlevelled Pure expression language. -/
inductive Expr where
  | sort
  | bvar : Nat → Expr
  | pi : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | app : Expr → Expr → Expr
  deriving DecidableEq, Repr

abbrev Ctx := List Expr

namespace Expr

/-- General de Bruijn lift by `distance` above `cutoff`. -/
def lift (distance cutoff : Nat) : Expr → Expr
  | .sort => .sort
  | .bvar index =>
      .bvar (if index < cutoff then index else index + distance)
  | .pi domain body =>
      .pi (lift distance cutoff domain) (lift distance (cutoff + 1) body)
  | .lam domain body =>
      .lam (lift distance cutoff domain) (lift distance (cutoff + 1) body)
  | .app fn arg => .app (lift distance cutoff fn) (lift distance cutoff arg)

/-- Capture-avoiding substitution for de Bruijn index `index`. -/
def subst (index : Nat) (replacement : Expr) : Expr → Expr
  | .sort => .sort
  | .bvar current =>
      if current = index then replacement
      else if index < current then .bvar (current - 1)
      else .bvar current
  | .pi domain body =>
      .pi (subst index replacement domain)
        (subst (index + 1) (lift 1 0 replacement) body)
  | .lam domain body =>
      .lam (subst index replacement domain)
        (subst (index + 1) (lift 1 0 replacement) body)
  | .app fn arg => .app (subst index replacement fn) (subst index replacement arg)

/-- Substitute an actual argument for the innermost telescope variable. -/
def subst0 (argument body : Expr) : Expr := subst 0 argument body

/-- Syntactic scope discipline; binders extend the de Bruijn depth. -/
inductive WellScoped : Nat → Expr → Prop where
  | sort {depth} : WellScoped depth .sort
  | bvar {depth index} : index < depth → WellScoped depth (.bvar index)
  | pi {depth domain body} :
      WellScoped depth domain →
      WellScoped (depth + 1) body →
      WellScoped depth (.pi domain body)
  | lam {depth domain body} :
      WellScoped depth domain →
      WellScoped (depth + 1) body →
      WellScoped depth (.lam domain body)
  | app {depth fn arg} :
      WellScoped depth fn → WellScoped depth arg →
      WellScoped depth (.app fn arg)

/-- Executable reflection of the syntactic scope discipline. -/
def wellScoped (depth : Nat) : Expr → Bool
  | .sort => true
  | .bvar index => decide (index < depth)
  | .pi domain body => wellScoped depth domain && wellScoped (depth + 1) body
  | .lam domain body => wellScoped depth domain && wellScoped (depth + 1) body
  | .app fn argument => wellScoped depth fn && wellScoped depth argument

/-- The executable scope checker is exact. -/
theorem wellScoped_eq_true_iff (depth : Nat) (expression : Expr) :
    expression.wellScoped depth = true ↔ WellScoped depth expression := by
  induction expression generalizing depth with
  | sort =>
      constructor
      · intro _
        exact WellScoped.sort
      · intro _
        rfl
  | bvar index =>
      constructor
      · intro hscoped
        exact WellScoped.bvar (of_decide_eq_true hscoped)
      · intro hscoped
        cases hscoped with
        | bvar hindex => exact decide_eq_true hindex
  | pi domain body domainIH bodyIH =>
      simp only [wellScoped, Bool.and_eq_true]
      constructor
      · rintro ⟨hdomain, hbody⟩
        exact WellScoped.pi
          ((domainIH depth).mp hdomain)
          ((bodyIH (depth + 1)).mp hbody)
      · intro hscoped
        cases hscoped with
        | pi hdomain hbody =>
            exact
              ⟨(domainIH depth).mpr hdomain,
                (bodyIH (depth + 1)).mpr hbody⟩
  | lam domain body domainIH bodyIH =>
      simp only [wellScoped, Bool.and_eq_true]
      constructor
      · rintro ⟨hdomain, hbody⟩
        exact WellScoped.lam
          ((domainIH depth).mp hdomain)
          ((bodyIH (depth + 1)).mp hbody)
      · intro hscoped
        cases hscoped with
        | lam hdomain hbody =>
            exact
              ⟨(domainIH depth).mpr hdomain,
                (bodyIH (depth + 1)).mpr hbody⟩
  | app fn argument fnIH argumentIH =>
      simp only [wellScoped, Bool.and_eq_true]
      constructor
      · rintro ⟨hfn, hargument⟩
        exact WellScoped.app
          ((fnIH depth).mp hfn)
          ((argumentIH depth).mp hargument)
      · intro hscoped
        cases hscoped with
        | app hfn hargument =>
            exact
              ⟨(fnIH depth).mpr hfn,
                (argumentIH depth).mpr hargument⟩

/-- Number of leading dependent arguments in a head type. -/
def piArity : Expr → Nat
  | .pi _ body => piArity body + 1
  | _ => 0

/-- Eta-long heads must end at a non-function target. -/
def Atomic : Expr → Prop
  | .pi _ _ => False
  | _ => True

def atomic : Expr → Bool
  | .pi _ _ => false
  | _ => true

theorem atomic_eq_true_iff (type : Expr) :
    type.atomic = true ↔ type.Atomic := by
  cases type <;> simp [atomic, Atomic]

end Expr

/-- Crossing a binder lifts older context declarations. -/
def ctxLookupAux : Nat → Ctx → Nat → Option Expr
  | _, [], _ => none
  | depth, domain :: _, 0 => some (domain.lift (depth + 1) 0)
  | depth, _ :: rest, index + 1 => ctxLookupAux (depth + 1) rest index

def ctxLookup (context : Ctx) (index : Nat) : Option Expr :=
  ctxLookupAux 0 context index

theorem ctxLookupAux_some_lt {depth : Nat} {context : Ctx}
    {index : Nat} {type : Expr}
    (hlookup : ctxLookupAux depth context index = some type) :
    index < context.length := by
  induction context generalizing depth index with
  | nil => simp [ctxLookupAux] at hlookup
  | cons domain rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [ctxLookupAux] at hlookup
          have hlt := ih hlookup
          simp only [List.length_cons]
          omega

theorem ctxLookup_some_lt {context : Ctx} {index : Nat} {type : Expr}
    (hlookup : ctxLookup context index = some type) :
    index < context.length :=
  ctxLookupAux_some_lt hlookup

/-- Beta-normal, eta-long inhabitants: lambdas or bound heads with ordered spines. -/
inductive Nf where
  | lam : Expr → Nf → Nf
  | head : Nat → List Nf → Nf
  deriving Repr

namespace Nf

/-- Erase the normal-form presentation into the shared Pure expression syntax. -/
def erase : Nf → Expr
  | .lam domain body => .lam domain body.erase
  | .head index arguments =>
      arguments.foldl (fun fn argument => .app fn argument.erase) (.bvar index)

mutual
/-- Termination measure for a normal form. -/
def weight : Nf → Nat
  | .lam _ body => body.weight + 1
  | .head _ arguments => listWeight arguments + 1

/-- Termination measure for an ordered argument spine. -/
def listWeight : List Nf → Nat
  | [] => 0
  | argument :: rest => argument.weight + listWeight rest + 1
end

end Nf

mutual
/-- Syntax-directed semantic typing of Pure normal forms. -/
inductive HasType : Ctx → Nf → Expr → Prop where
  | lam {context domain body bodyType} :
      HasType (domain :: context) body bodyType →
      HasType context (.lam domain body) (.pi domain bodyType)
  | head {context index headType arguments resultType} :
      ctxLookup context index = some headType →
      SpineHasType context headType arguments resultType →
      resultType.Atomic →
      HasType context (.head index arguments) resultType

/-- Ordered dependent application: every later type sees earlier arguments substituted. -/
inductive SpineHasType : Ctx → Expr → List Nf → Expr → Prop where
  | nil {context headType} : SpineHasType context headType [] headType
  | cons {context domain body argument rest resultType} :
      HasType context argument domain →
      SpineHasType context (Expr.subst0 argument.erase body) rest resultType →
      SpineHasType context (.pi domain body) (argument :: rest) resultType
end

mutual
/-- Fuelled inference for normal forms; equality is syntactic, never conversion. -/
def inferNfFuel : Nat → Ctx → Nf → Option Expr
  | 0, _, _ => none
  | fuel + 1, context, .lam domain body =>
      (inferNfFuel fuel (domain :: context) body).map fun bodyType =>
        .pi domain bodyType
  | fuel + 1, context, .head index arguments => do
      let headType ← ctxLookup context index
      let resultType ← inferSpineFuel fuel context headType arguments
      if resultType.atomic then some resultType else none

/-- Fuelled dependent-spine checker. -/
def inferSpineFuel : Nat → Ctx → Expr → List Nf → Option Expr
  | 0, _, _, _ => none
  | _fuel + 1, _, headType, [] => some headType
  | fuel + 1, context, .pi domain body, argument :: rest => do
      let actual ← inferNfFuel fuel context argument
      if actual = domain then
        inferSpineFuel fuel context (Expr.subst0 argument.erase body) rest
      else
        none
  | _fuel + 1, _, _, _ :: _ => none
end

/-- Total checker fuel computed from the whole normal form. -/
def inferNf (context : Ctx) (term : Nf) : Option Expr :=
  inferNfFuel (term.weight + 1) context term

/-- Total checker fuel computed from the whole argument list. -/
def inferSpine (context : Ctx) (headType : Expr)
    (arguments : List Nf) : Option Expr :=
  inferSpineFuel (Nf.listWeight arguments + 1) context headType arguments

/-- Simultaneous soundness of the fuelled term and spine checkers. -/
theorem inferFuel_sound : ∀ fuel,
    (∀ context term type,
      inferNfFuel fuel context term = some type → HasType context term type) ∧
    (∀ context headType arguments resultType,
      inferSpineFuel fuel context headType arguments = some resultType →
        SpineHasType context headType arguments resultType) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;> simp [inferNfFuel, inferSpineFuel]
  | succ fuel ih =>
      constructor
      · intro context term type hinfer
        cases term with
        | lam domain body =>
            simp only [inferNfFuel, Option.map_eq_some_iff] at hinfer
            rcases hinfer with ⟨bodyType, hbody, rfl⟩
            exact HasType.lam (ih.1 _ _ _ hbody)
        | head index arguments =>
            simp only [inferNfFuel] at hinfer
            cases hlookup : ctxLookup context index with
            | none => simp [hlookup] at hinfer
            | some headType =>
                simp only [hlookup] at hinfer
                cases hspine : inferSpineFuel fuel context headType arguments with
                | none => simp [hspine] at hinfer
                | some resultType =>
                    by_cases hatomic : resultType.atomic = true
                    · simp [hspine, hatomic] at hinfer
                      subst type
                      exact HasType.head hlookup (ih.2 _ _ _ _ hspine)
                        ((Expr.atomic_eq_true_iff resultType).mp hatomic)
                    · simp [hspine, hatomic] at hinfer
      · intro context headType arguments resultType hinfer
        cases arguments with
        | nil =>
            simp only [inferSpineFuel, Option.some.injEq] at hinfer
            subst resultType
            exact SpineHasType.nil
        | cons argument rest =>
            cases headType with
            | pi domain body =>
                cases hargument : inferNfFuel fuel context argument with
                | none => simp [inferSpineFuel, hargument] at hinfer
                | some actual =>
                    by_cases htype : actual = domain
                    · simp [inferSpineFuel, hargument, htype] at hinfer
                      subst actual
                      exact SpineHasType.cons (ih.1 _ _ _ hargument)
                        (ih.2 _ _ _ _ hinfer)
                    · simp [inferSpineFuel, hargument, htype] at hinfer
            | sort => simp [inferSpineFuel] at hinfer
            | bvar index => simp [inferSpineFuel] at hinfer
            | lam domain body => simp [inferSpineFuel] at hinfer
            | app fn arg => simp [inferSpineFuel] at hinfer

/-- Simultaneous bounded completeness of the fuelled term and spine checkers. -/
theorem inferFuel_complete : ∀ fuel,
    (∀ context term type,
      term.weight < fuel → HasType context term type →
        inferNfFuel fuel context term = some type) ∧
    (∀ context headType arguments resultType,
      Nf.listWeight arguments < fuel →
      SpineHasType context headType arguments resultType →
        inferSpineFuel fuel context headType arguments = some resultType) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;> omega
  | succ fuel ih =>
      constructor
      · intro context term type hweight htype
        cases htype with
        | lam hbody =>
            simp only [Nf.weight] at hweight
            simp [inferNfFuel, ih.1 _ _ _ (by omega) hbody]
        | head hlookup hspine hatomic =>
            simp only [Nf.weight] at hweight
            simp [inferNfFuel, hlookup, ih.2 _ _ _ _ (by omega) hspine,
              (Expr.atomic_eq_true_iff _).mpr hatomic]
      · intro context headType arguments resultType hweight htype
        cases htype with
        | nil => simp [inferSpineFuel]
        | cons hargument hrest =>
            simp only [Nf.listWeight] at hweight
            simp [inferSpineFuel,
              ih.1 _ _ _ (by omega) hargument,
              ih.2 _ _ _ _ (by omega) hrest]

/-- Algorithmic inference is sound for the semantic normal-form judgment. -/
theorem inferNf_sound {context : Ctx} {term : Nf} {type : Expr}
    (hinfer : inferNf context term = some type) :
    HasType context term type :=
  (inferFuel_sound (term.weight + 1)).1 _ _ _ hinfer

/-- Algorithmic spine inference is sound and preserves argument order. -/
theorem inferSpine_sound {context : Ctx} {headType : Expr}
    {arguments : List Nf} {resultType : Expr}
    (hinfer : inferSpine context headType arguments = some resultType) :
    SpineHasType context headType arguments resultType :=
  (inferFuel_sound (Nf.listWeight arguments + 1)).2 _ _ _ _ hinfer

/-- The executable checker is complete for the semantic normal-form judgment. -/
theorem inferNf_complete {context : Ctx} {term : Nf} {type : Expr}
    (htype : HasType context term type) :
    inferNf context term = some type :=
  (inferFuel_complete (term.weight + 1)).1 _ _ _ (by omega) htype

/-- Completeness of ordered dependent-spine checking. -/
theorem inferSpine_complete {context : Ctx} {headType : Expr}
    {arguments : List Nf} {resultType : Expr}
    (htype : SpineHasType context headType arguments resultType) :
    inferSpine context headType arguments = some resultType :=
  (inferFuel_complete (Nf.listWeight arguments + 1)).2 _ _ _ _ (by omega) htype

/-- The checker exposes semantic typing as an exact executable equivalence. -/
theorem inferNf_eq_some_iff {context : Ctx} {term : Nf} {type : Expr} :
    inferNf context term = some type ↔ HasType context term type :=
  ⟨inferNf_sound, inferNf_complete⟩

/-- The sigma-crux: after one argument, the next slot uses actual substitution. -/
theorem dependent_spine_tail {context : Ctx} {domain body : Expr}
    {argument : Nf} {rest : List Nf} {resultType : Expr}
    (htype : SpineHasType context (.pi domain body)
      (argument :: rest) resultType) :
    HasType context argument domain ∧
      SpineHasType context (Expr.subst0 argument.erase body) rest resultType := by
  cases htype with
  | cons hargument hrest => exact ⟨hargument, hrest⟩

/-! ## Positive and negative dependent-spine fixtures -/

def fixtureA : Expr := .sort
def fixtureFamily : Expr := .pi (.bvar 0) .sort
def fixtureHeadType : Expr :=
  .pi (.bvar 2) (.app (.bvar 2) (.bvar 0))
def fixturePx : Expr := .app (.bvar 2) (.bvar 1)

/-- Context: `h : (a : A) → P a`, `x : A`, `P : A → Type`, `A : Type`. -/
def fixtureContext : Ctx :=
  [fixtureHeadType, .bvar 1, fixtureFamily, fixtureA]

example : ctxLookup fixtureContext 1 = some (.bvar 3) := by decide

/-- `h` applied to `x` has the substituted type `P x`. -/
example :
    inferNf fixtureContext (.head 0 [.head 1 []]) = some fixturePx := by
  norm_num [inferNf, inferNfFuel, inferSpineFuel, Nf.weight, Nf.listWeight,
    Nf.erase, ctxLookup, ctxLookupAux, fixtureContext, fixtureHeadType,
    fixtureFamily, fixtureA, fixturePx, Expr.atomic, Expr.lift, Expr.subst0,
    Expr.subst]

/-- Swapping in the type-family `P` where an `A` argument is required is rejected. -/
example :
    inferNf fixtureContext (.head 0 [.head 2 []]) = none := by
  norm_num [inferNf, inferNfFuel, inferSpineFuel, Nf.weight, Nf.listWeight,
    Nf.erase, ctxLookup, ctxLookupAux, fixtureContext, fixtureHeadType,
    fixtureFamily, fixtureA, Expr.atomic, Expr.lift, Expr.subst0, Expr.subst]

end Mettapedia.GSLT.LanguageDef.Pure
