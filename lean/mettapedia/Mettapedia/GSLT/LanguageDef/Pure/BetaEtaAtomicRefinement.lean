/-
# Conversion-aware atomic refinement for Pure

The policy still emits only `Refine(hole, head)`.  Deterministic elaboration
owns lambdas and ordered dependent spines.  Unlike the syntactic Pure root,
independent terminal inference compares types by the proved beta-eta
conversion test.
-/

import Mettapedia.GSLT.LanguageDef.Pure.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaConversion

namespace Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBetaEta

/-- A result type is atomic after beta reduction. -/
def BetaAtomic (type : Expr) : Prop :=
  ∃ reduced, Reduces type reduced ∧ reduced.Atomic

def betaAtomic (type : Expr) : Bool :=
  (betaNf normalizationFuel type).atomic

theorem betaAtomic_sound {type : Expr} (hatomic : betaAtomic type = true) :
    BetaAtomic type := by
  refine ⟨betaNf normalizationFuel type, betaNf_sound _ _, ?_⟩
  exact (Expr.atomic_eq_true_iff _).mp hatomic

mutual
/-- Conversion-aware normal-form typing for the universe-free Pure calculus. -/
inductive HasType : Ctx → Nf → Expr → Prop where
  | lam {context domain body bodyType} :
      HasType (domain :: context) body bodyType →
      HasType context (.lam domain body) (.pi domain bodyType)
  | head {context index headType arguments resultType} :
      ctxLookup context index = some headType →
      SpineHasType context headType arguments resultType →
      BetaAtomic resultType →
      HasType context (.head index arguments) resultType

/-- Ordered dependent application with beta-eta conversion at each slot. -/
inductive SpineHasType : Ctx → Expr → List Nf → Expr → Prop where
  | nil {context headType} : SpineHasType context headType [] headType
  | cons {context domain body argument actualType rest resultType} :
      HasType context argument actualType →
      Conv actualType domain →
      SpineHasType context (Expr.subst0 argument.erase body) rest resultType →
      SpineHasType context (.pi domain body) (argument :: rest) resultType
end

mutual
/-- Fuelled conversion-aware inference for normal forms. -/
def inferNfFuel : Nat → Ctx → Nf → Option Expr
  | 0, _, _ => none
  | fuel + 1, context, .lam domain body =>
      (inferNfFuel fuel (domain :: context) body).map fun bodyType =>
        .pi domain bodyType
  | fuel + 1, context, .head index arguments => do
      let headType ← ctxLookup context index
      let resultType ← inferSpineFuel fuel context headType arguments
      if betaAtomic resultType then some resultType else none

/-- Fuelled ordered-spine inference with conversion-aware argument checking. -/
def inferSpineFuel : Nat → Ctx → Expr → List Nf → Option Expr
  | 0, _, _, _ => none
  | _fuel + 1, _, headType, [] => some headType
  | fuel + 1, context, .pi domain body, argument :: rest => do
      let actualType ← inferNfFuel fuel context argument
      if convBool actualType domain then
        inferSpineFuel fuel context (Expr.subst0 argument.erase body) rest
      else
        none
  | _fuel + 1, _, _, _ :: _ => none
end

def inferNf (context : Ctx) (term : Nf) : Option Expr :=
  inferNfFuel (term.weight + 1) context term

def inferSpine (context : Ctx) (headType : Expr)
    (arguments : List Nf) : Option Expr :=
  inferSpineFuel (Nf.listWeight arguments + 1) context headType arguments

theorem inferFuel_sound : ∀ fuel,
    (∀ context term type,
      inferNfFuel fuel context term = some type → HasType context term type) ∧
    (∀ context headType arguments resultType,
      inferSpineFuel fuel context headType arguments = some resultType →
        SpineHasType context headType arguments resultType) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;> simp [inferNfFuel, inferSpineFuel] at *
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
                    by_cases hatomic : betaAtomic resultType = true
                    · simp [hspine, hatomic] at hinfer
                      subst type
                      exact HasType.head hlookup (ih.2 _ _ _ _ hspine)
                        (betaAtomic_sound hatomic)
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
                | some actualType =>
                    by_cases hconv : convBool actualType domain = true
                    · simp [inferSpineFuel, hargument, hconv] at hinfer
                      exact SpineHasType.cons
                        (ih.1 _ _ _ hargument)
                        (convBool_sound hconv)
                        (ih.2 _ _ _ _ hinfer)
                    · simp [inferSpineFuel, hargument, hconv] at hinfer
            | sort => simp [inferSpineFuel] at hinfer
            | bvar index => simp [inferSpineFuel] at hinfer
            | lam domain body => simp [inferSpineFuel] at hinfer
            | app fn argument => simp [inferSpineFuel] at hinfer

theorem inferNf_sound {context : Ctx} {term : Nf} {type : Expr}
    (hinfer : inferNf context term = some type) : HasType context term type :=
  (inferFuel_sound (term.weight + 1)).1 _ _ _ hinfer

theorem inferSpine_sound {context : Ctx} {headType : Expr}
    {arguments : List Nf} {resultType : Expr}
    (hinfer : inferSpine context headType arguments = some resultType) :
    SpineHasType context headType arguments resultType :=
  (inferFuel_sound (Nf.listWeight arguments + 1)).2 _ _ _ _ hinfer

/-- Deliver a subterm through continuations, comparing types by beta-eta conversion. -/
def deliver : Nf → List Frame → Option Core
  | term, [] => some (.done term)
  | term, .lambda domain :: rest => deliver (.lam domain term) rest
  | term, .spine context head arguments body expected :: rest =>
      let arguments := arguments ++ [term]
      let application := Nf.head head arguments
      let nextType := Expr.subst0 term.erase body
      if convBool nextType expected then
        deliver application rest
      else
        match nextType with
        | .pi domain nextBody =>
            some (prepare 0 context domain
              (.spine context head arguments nextBody expected :: rest))
        | _ => none

/-- Start a checker-owned dependent spine under conversion. -/
def startSpine (context : Ctx) (expected : Expr) (frames : List Frame)
    (head : Nat) (arguments : List Nf) : Expr → Option Core
  | .pi domain body =>
      some (prepare 0 context domain
        (.spine context head arguments body expected :: frames))
  | headType =>
      if convBool headType expected then deliver (.head head arguments) frames
      else none

/-- One conversion-aware `Refine(hole, head)` transition. -/
def rawRefine? (core : Core) (action : AtomicAction) : Option Core := do
  let forced ← forcedLegacyActions? core action
  match forced, core with
  | [.selectHole _, .selectBoundHead _, .createDependentSpine _],
      .needHole _ context expected frames => do
      let headType ← ctxLookup context action.head
      startSpine context expected frames action.head [] headType
  | _, _ => none

def rawRunAtomic : List AtomicAction → Core → Option Core
  | [], core => some core
  | action :: rest, core => do
      let next ← rawRefine? core action
      rawRunAtomic rest next

/-- Decode only after independent conversion-aware inference of the final term. -/
def decode (goal : Expr) (trace : List AtomicAction) : Option Nf :=
  match rawRunAtomic trace (prepare 0 [] goal []) with
  | some (.done term) =>
      match inferNf [] term with
      | some inferred => if convBool inferred goal then some term else none
      | none => none
  | _ => none

/-- Accepted traces produce independently typed inhabitants modulo beta-eta conversion. -/
theorem decode_sound {goal : Expr} {trace : List AtomicAction} {term : Nf}
    (hdecode : decode goal trace = some term) :
    ∃ inferred, HasType [] term inferred ∧ Conv inferred goal := by
  unfold decode at hdecode
  cases hrun : rawRunAtomic trace (prepare 0 [] goal []) with
  | none => simp [hrun] at hdecode
  | some core =>
      cases core with
      | needHole hole context target frames => simp [hrun] at hdecode
      | needHead hole context target frames => simp [hrun] at hdecode
      | needSpine hole context target frames head headType => simp [hrun] at hdecode
      | finished finalTerm => simp [hrun] at hdecode
      | done finalTerm =>
          cases hinfer : inferNf [] finalTerm with
          | none => simp [hrun, hinfer] at hdecode
          | some inferred =>
              by_cases hconv : convBool inferred goal = true
              · simp [hrun, hinfer, hconv] at hdecode
                subst term
                exact ⟨inferred, inferNf_sound hinfer, convBool_sound hconv⟩
              · simp [hrun, hinfer, hconv] at hdecode

/-! Positive and negative trace fixtures at the conversion boundary. -/

def identityGoal : Expr := .pi .sort .sort

example : (decode identityGoal [⟨0, 0⟩]).isSome = true := by decide

example : (decode identityGoal [⟨0, 1⟩]).isSome = false := by decide

end Mettapedia.GSLT.LanguageDef.PureBetaEtaRefinement
