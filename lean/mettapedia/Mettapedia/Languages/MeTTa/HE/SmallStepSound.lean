import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# Small-Step Soundness Against the Official Declarative Spec

First slice of the small-step / official-HE correspondence: the coarse
root computational rules of `HESmallStep` are **absorbed** by the official
declarative semantics (`EvalSpec.lean`'s `MettaCall`), in the classic
small-step-composes-into-big-step sense:

> if `a` coarse-steps to `b` by a root rule, and the official semantics
> evaluates `b` (under the step's bindings) to a final result, then the
> official `MettaCall` evaluates `a` to the same result.

Covered here: `HES_GroundedDispatch` (`mettaCall_absorbs_grounded_dispatch`),
`HES_EquationMatch` (`mettaCall_absorbs_equation_match`), and `HES_Eval`
(`minimalStep_absorbs_eval`, against the official `MinimalStep.eval`
instruction).  These are the Lean soundness theorems behind those rules'
`rule-sound` claim level in the runtime rule table (`lts:he:step-rules`).

Not covered yet (their claim level stays `bag-tested-adequate`), and the
single master theorem they all funnel through:

> **EvalAtom absorbs coarse steps** — if `a` coarse-steps to `b`, official
> evaluation of `b` yields official evaluation of `a`; with the companion
> **quiescent self-evaluation** — coarse normal forms officially evaluate
> to themselves.

Its congruence case is the `InterpretTuple`/`InterpretArgs` context lemma;
`HES_Chain`'s two cases need respectively the master statement (source
progress) and quiescent self-evaluation (substitution); `let`/`let*`/`case`/
`switch` additionally need their stdlib-sugar semantics pinned before
modeling.  We state only what we prove.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Merging any bindings with the empty bindings (on the right) is the
identity, at any positive fuel: the merge folds over the right side's
(empty) assignment and equality lists. -/
theorem mergeBindings_empty_right (b : Bindings) (n : Nat) :
    mergeBindings b Bindings.empty (n + 1) = [b] := by
  simp [mergeBindings, Bindings.empty]

/-- At fuel zero the equation query is empty: `simpleMatch` refuses to match
without fuel, so no equation can fire.  (Hence fuel-zero coarse equation
steps are impossible, and the absorption theorem needs no fuel premise.) -/
theorem queryEquations_zero (space : Space) (a : Atom) :
    queryEquations space a 0 = [] := by
  simp only [queryEquations, List.filterMap_eq_nil_iff]
  intro p _hp
  split
  · simp [simpleMatch]
  · rfl

/-- **Absorption, grounded dispatch.**  A coarse `HES_GroundedDispatch` step
from `(op args…)` to result atom `r` (with result bindings `bs`) composes
with any official evaluation of `r` under `bs` into an official `MettaCall`
of the original expression under empty bindings.  This is the Lean
soundness theorem behind `HES_GroundedDispatch`'s `rule-sound` claim. -/
theorem mettaCall_absorbs_grounded_dispatch
    {space : Space} {d : GroundedDispatch}
    {op : Atom} {args : List Atom} {rs : ResultSet} {r : Atom} {bs : Bindings}
    {type_ : Atom} {finalResult : ResultPair} (fuel : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression (op :: args)))
    (h_exec : d.isExecutable op = true)
    (h_run : d.execute op args = .ok rs)
    (h_mem : (r, bs) ∈ rs)
    (h_not_err : isErrorAtom (.expression (op :: args)) = false)
    (h_eval : EvalAtom space d r type_ bs finalResult) :
    MettaCall space d (.expression (op :: args)) type_ Bindings.empty
      finalResult :=
  MettaCall.grounded_ok (.expression (op :: args)) type_ Bindings.empty
    op args rs (r, bs) bs finalResult (fuel + 1)
    rfl h_exec
    (by
      intro h_unify
      apply h_not_special
      simp [SpecialFormHead, h_unify])
    (by
      intro h_switch
      apply h_not_special
      simp [SpecialFormHead, h_switch])
    h_not_err h_run h_mem
    (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
    h_eval

/-- **Absorption, equation match.**  A coarse `HES_EquationMatch` step from
`(es…)` to `qb.apply rhs fuel` composes with any official evaluation of that
successor under `qb` into an official `MettaCall` of the original expression
under empty bindings.  This is the Lean soundness theorem behind
`HES_EquationMatch`'s `rule-sound` claim.

The coarse rule's premises are exactly the official ones: the query
membership and the head-not-executable priority come from
`MettaCall.equation_match` itself, and the coarse rule's `h_no_loop` side
condition discharges the official `hasLoop` requirement (with empty incoming
bindings, the merged bindings are the query bindings). -/
theorem mettaCall_absorbs_equation_match
    {space : Space} {d : GroundedDispatch}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {type_ : Atom} {finalResult : ResultPair} {fuel : Nat}
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
    (h_no_loop : qb.hasLoop = false)
    (h_not_err : isErrorAtom (.expression es) = false)
    (h_eval : EvalAtom space d (qb.apply rhs fuel) type_ qb finalResult) :
    MettaCall space d (.expression es) type_ Bindings.empty finalResult := by
  cases fuel with
  | zero =>
      rw [queryEquations_zero] at h_query
      cases h_query
  | succ n =>
      exact MettaCall.equation_match (.expression es) type_ Bindings.empty
        rhs qb qb finalResult (n + 1)
        h_not_err
        (by
          revert h_not_grounded
          unfold HeadNotExecutable
          cases es with
          | nil => intro h; exact h
          | cons op rest => intro h; exact h)
        h_query
        (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
        h_no_loop
        h_eval

/-- Packaging both root rules: any root coarse step (grounded dispatch or
equation match, as produced by `HESmallStep`'s first two constructors)
composes with official evaluation of its successor into an official
`MettaCall` of the source.  The bindings under which the successor is
evaluated are the step's own witness bindings. -/
theorem mettaCall_absorbs_root_step
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {a b : Atom} (h : HESmallStep space d fuel a b)
    (h_not_err : isErrorAtom a = false)
    (h_not_special : ¬ SpecialFormHead a)
    (h_root : ∀ {pre x x' post}, a = Atom.expression (pre ++ x :: post) →
      b = Atom.expression (pre ++ x' :: post) → False) :
    ∃ bnd, ∀ {type_ : Atom} {finalResult : ResultPair},
      EvalAtom space d b type_ bnd finalResult →
      MettaCall space d a type_ Bindings.empty finalResult := by
  cases h with
  | @grounded_dispatch op args rs r bs _ h_exec h_run h_mem =>
      exact ⟨bs, fun h_eval =>
        mettaCall_absorbs_grounded_dispatch fuel h_not_special h_exec h_run h_mem
          h_not_err h_eval⟩
  | @equation_match es rhs qb _ h_not_grounded h_query h_no_loop =>
      exact ⟨qb, fun h_eval =>
        mettaCall_absorbs_equation_match h_not_grounded h_query h_no_loop
          h_not_err h_eval⟩
  | eval_step h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | chain_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | chain_subst h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_return h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | function_no_return h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | letStar_empty h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | letStar_unroll h_shape =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | let_source h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | let_subst h_shape _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | case_scrutinee h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | case_match h_shape _ _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_scrutinee h_shape _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_match h_shape _ _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | switch_minimal_match h_shape _ _ _ =>
      exact absurd (by simp [SpecialFormHead, h_shape]) h_not_special
  | @leftmost_congruence pre x x' post _ _ _ _ _ =>
      exact absurd rfl (fun h' => h_root h' rfl)

/-- **Absorption, eval.**  The coarse `HES_Eval` rule steps `(eval E)` to
`E`; the official `MinimalStep.eval` instruction evaluates `(eval E)` by
evaluating `E`.  So any official evaluation of the coarse successor IS an
official result of the instruction — the rule's content is exactly the
official constructor.  This is the Lean soundness theorem behind
`HES_Eval`'s `rule-sound` claim. -/
theorem minimalStep_absorbs_eval
    {space : Space} {d : GroundedDispatch}
    {e : Atom} {ib : Bindings} {r : ResultPair}
    (h_eval : EvalAtom space d e Atom.undefinedType ib r) :
    MinimalStep d space (.expression [.symbol "eval", e]) ib space r :=
  MinimalStep.eval space e ib r h_eval

end Mettapedia.Languages.MeTTa.HE
