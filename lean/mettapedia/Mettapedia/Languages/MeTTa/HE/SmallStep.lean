import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# HE Small-Step: The Coarse User-Visible One-Step Relation

The **HE small-step** granularity stratum (user-visible surface steps): one
observable surface rewrite over ordinary MeTTa atoms, e.g.
`(+ 1 (+ 2 3)) → (+ 1 5)`.  This is the relation that CeTTa's
`lts:he:transitions` surface exposes and that the runtime HE small-step rule
table drives.

This Lean model now mirrors **all ten** of the table's live rules:
`HES_GroundedDispatch`, `HES_EquationMatch` (via the official
`queryEquations`), `HES_Eval`, `HES_Chain` (source-progress +
substitution), `HES_Let` (source-progress + `simpleMatch` substitution),
`HES_LetStar` (empty + unroll desugaring), `HES_Case` (scrutinee-progress
+ first-matching-branch), `HES_Switch` (scrutinee-progress +
branch-selection — the scrutinee is evaluated per the upstream contract),
`HES_SwitchMinimal` (structural match on the raw scrutinee), and
`HES_LeftmostExprCongruence` — with the
runtime's rule priority encoded (special forms before grounded before
equations before congruence).  The relation is the *visible* step
relation: evaluation-to-Empty (e.g. no-match `let`/`case`/`switch`)
appears as quiescence, per the Empty-as-absorbing-zero doctrine.
Degenerate special-form arities (e.g. a two-argument `chain`) are outside
the modeled fragment.  In addition, this file carries a local
`function`/`return` continuation scaffold for the switch-internal
proofs: `function` steps its body, unwraps a quiescent `(return ...)`, or
produces `NoReturn`, while bare `return` stays an inert control sentinel.

This is **not** the fine `mettaHE` instruction machine (`HELanguageDef.lean`,
which steps interpreter states `Metta/InterpExpr/...`), and **not** big-step
evaluation.  The collapse/simulation theorems relating the small-step
relation to the fine machine (delimited observable closure) are deliberately
*not stated here* — they are future work with real content, and we state
only what we prove.

## Main definitions

* `GroundedRedex` — the head is an executable grounded operation that the
  dispatch oracle reduces (provenance: `M_Expression`, `IE_*`, `IF_*`,
  `MC_Grounded`).
* `EquationRedex` — a non-grounded-headed expression with at least one
  matching `(= lhs rhs)` equation in the space (provenance: `MC_Equation`).
  Stated via `queryEquations _ _ _ ≠ []`, which is decidable, so witnesses
  can be checked by `decide`.
* `HECanSmallStep` — positive inductive *steppability* (used to express
  leftmostness without a non-positive occurrence).
* `HESmallStep` — the coarse step relation; rule priority matches the
  runtime: grounded dispatch, else equation match, else leftmost argument
  congruence.
* `heSmallStepSpan` — the OSLF `ReductionSpan` over `HESmallStep`, giving
  `derivedDiamond`/`derivedBox` and the Galois connection for free.
* `successorBox` — the *successor* box (`lts:he:box` in the runtime), the
  De Morgan dual of `derivedDiamond`; OSLF's `derivedBox` is the
  *predecessor* box (the Galois adjoint).  Both are stated precisely.

## Runtime correspondence

The runtime self-tests mirror the lemmas here:
`lts:he:is-can-step` ↔ `diamond_top_iff_exists_step`,
`lts:he:is-normal-form` ↔ `normalForm_iff_successorBox_false`,
the `box φ = not (diamond (not φ))` self-test ↔
`successorBox_iff_not_diamond_not`, and the `◇ ⊣ □` adjunction ↔
`heSmallStep_galois`.

The grounded oracle is the same `GroundedDispatch` and the equation query is
the same `queryEquations` that `EvalSpec.lean` uses; nothing is faked inside
the relation.  `fuel` indexes the equation-matching depth exactly as in the
executable spec.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Redex predicates -/

/-- `a` is a grounded redex: its head is an executable grounded operation and
the dispatch oracle reduces it to at least one result. -/
def GroundedRedex (d : GroundedDispatch) (a : Atom) : Prop :=
  ∃ op args rs r bs,
    a = .expression (op :: args) ∧
    d.isExecutable op = true ∧
    d.execute op args = .ok rs ∧
    (r, bs) ∈ rs

/-- The head of `a` is not an executable grounded operation (the priority
condition `EvalSpec.lean`'s `MettaCall.equation_match` imposes). -/
def HeadNotExecutable (d : GroundedDispatch) (a : Atom) : Prop :=
  match a with
  | .expression (op :: _) =>
      d.isExecutable op = false ∧
      op ≠ .symbol "unify" ∧
      op ≠ .symbol "switch-minimal"
  | _ => True

/-- `a` is headed by one of the special-form symbols the runtime dispatches
before grounded/equation/congruence.  Mirrors the C priority: special forms
never reach grounded dispatch, equation matching, or congruence. -/
def SpecialFormHead (a : Atom) : Prop :=
  match a with
  | .expression (.symbol s :: _) =>
      s = "eval" ∨ s = "chain" ∨ s = "let" ∨ s = "let*" ∨ s = "case" ∨
      s = "switch" ∨ s = "switch-minimal" ∨ s = "unify" ∨
      s = "function" ∨ s = "return"
  | _ => False

/-- `a` is an equation redex: a non-grounded-headed expression with at least
one matching `(= lhs rhs)` equation in the space.  `queryEquations` is the
official query from `Space.lean` (alpha-freshened, `simpleMatch`-based). -/
def EquationRedex (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (a : Atom) : Prop :=
  (∃ es, a = .expression es) ∧
  ¬ SpecialFormHead a ∧
  HeadNotExecutable d a ∧
  ∃ p ∈ queryEquations space a fuel, p.2.hasLoop = false

/-! ## Steppability (positive polarity)

`HESmallStep`'s leftmost-congruence rule needs "earlier siblings cannot
step".  Saying `¬ HESmallStep b b'` inside `HESmallStep`'s own constructor
would be a non-positive occurrence, so steppability is defined first as its
own positive inductive; `canStep_of_step` then proves that
`¬ HECanSmallStep` really does imply "no step". -/

/-- Steppability for the three-rule HE small-step fragment: an atom can step
iff it is a grounded redex, an equation redex, or some element of it can
step. -/
inductive HECanSmallStep (space : Space) (d : GroundedDispatch) (fuel : Nat) :
    Atom → Prop where
  | grounded {a : Atom} (h_not_special : ¬ SpecialFormHead a)
      (h : GroundedRedex d a) :
      HECanSmallStep space d fuel a
  | equation {a : Atom} (h : EquationRedex space d fuel a) :
      HECanSmallStep space d fuel a
  | eval_form {es : List Atom} {e : Atom}
      (h_shape : es = [.symbol "eval", e]) :
      HECanSmallStep space d fuel (.expression es)
  | chain_form {es : List Atom} {a : Atom} {v : String} {t : Atom}
      (h_shape : es = [.symbol "chain", a, .var v, t]) :
      HECanSmallStep space d fuel (.expression es)
  | function_form {es : List Atom} {body : Atom}
      (h_shape : es = [.symbol "function", body]) :
      HECanSmallStep space d fuel (.expression es)
  | letStar_empty_form {es : List Atom} {body : Atom}
      (h_shape : es = [.symbol "let*", .expression [], body]) :
      HECanSmallStep space d fuel (.expression es)
  | letStar_unroll_form {es : List Atom} {pt vt body : Atom} {rest : List Atom}
      (h_shape : es = [.symbol "let*",
        .expression (.expression [pt, vt] :: rest), body]) :
      HECanSmallStep space d fuel (.expression es)
  | let_source_form {es : List Atom} {pt v body : Atom}
      (h_shape : es = [.symbol "let", pt, v, body])
      (h_can : HECanSmallStep space d fuel v) :
      HECanSmallStep space d fuel (.expression es)
  | let_subst_form {es : List Atom} {pt v body : Atom}
      (h_shape : es = [.symbol "let", pt, v, body])
      (h_match : ∃ mb, simpleMatch pt v Bindings.empty fuel = some mb) :
      HECanSmallStep space d fuel (.expression es)
  | case_scrutinee_form {es : List Atom} {scrut branches : Atom}
      (h_shape : es = [.symbol "case", scrut, branches])
      (h_can : HECanSmallStep space d fuel scrut) :
      HECanSmallStep space d fuel (.expression es)
  | case_match_form {es : List Atom} {scrut : Atom} {branches : List Atom}
      (h_shape : es = [.symbol "case", scrut, .expression branches])
      (h_can : ∃ (i : Nat) (pt t : Atom) (mb : Bindings),
        branches[i]? = some (Atom.expression [pt, t]) ∧
        simpleMatch pt scrut Bindings.empty fuel = some mb ∧
        ∀ j < i, ∀ pt' t', branches[j]? = some (Atom.expression [pt', t']) →
          simpleMatch pt' scrut Bindings.empty fuel = none) :
      HECanSmallStep space d fuel (.expression es)
  | switch_scrutinee_form {es : List Atom} {scrut branches : Atom}
      (h_shape : es = [.symbol "switch", scrut, branches])
      (h_can : HECanSmallStep space d fuel scrut) :
      HECanSmallStep space d fuel (.expression es)
  | switch_match_form {es : List Atom} {scrut : Atom} {branches : List Atom}
      (h_shape : es = [.symbol "switch", scrut, .expression branches])
      (h_can : ∃ (i : Nat) (pt t : Atom) (mb : Bindings),
        branches[i]? = some (Atom.expression [pt, t]) ∧
        simpleMatch pt scrut Bindings.empty fuel = some mb ∧
        ∀ j < i, ∀ pt' t', branches[j]? = some (Atom.expression [pt', t']) →
          simpleMatch pt' scrut Bindings.empty fuel = none) :
      HECanSmallStep space d fuel (.expression es)
  | switch_minimal_form {es : List Atom} {scrut : Atom} {branches : List Atom}
      (h_shape : es = [.symbol "switch-minimal", scrut, .expression branches])
      (h_can : ∃ (i : Nat) (pt t : Atom) (mb : Bindings),
        branches[i]? = some (Atom.expression [pt, t]) ∧
        simpleMatch pt scrut Bindings.empty fuel = some mb ∧
        ∀ j < i, ∀ pt' t', branches[j]? = some (Atom.expression [pt', t']) →
          simpleMatch pt' scrut Bindings.empty fuel = none) :
      HECanSmallStep space d fuel (.expression es)
  | element {es : List Atom} {e : Atom}
      (h_not_special : ¬ SpecialFormHead (.expression es))
      (h_mem : e ∈ es) (h_e : HECanSmallStep space d fuel e) :
      HECanSmallStep space d fuel (.expression es)

/-! ## The coarse step relation -/

/-- One coarse HE small-step.  Rule priority matches the runtime: grounded
dispatch fires at the root; otherwise a matching equation fires; otherwise
the leftmost steppable element steps (deterministic left-to-right argument
congruence). -/
inductive HESmallStep (space : Space) (d : GroundedDispatch) (fuel : Nat) :
    Atom → Atom → Prop where
  /-- `HES_GroundedDispatch`: the head is an executable grounded operation
  and `r` is one of the dispatch results.  Relational: every result in the
  returned set is a successor. -/
  | grounded_dispatch {op : Atom} {args : List Atom} {rs : ResultSet}
      {r : Atom} {bs : Bindings}
      (h_not_special : ¬ SpecialFormHead (.expression (op :: args)))
      (h_exec : d.isExecutable op = true)
      (h_run : d.execute op args = .ok rs)
      (h_mem : (r, bs) ∈ rs) :
      HESmallStep space d fuel (.expression (op :: args)) r
  /-- `HES_Eval`: `(eval E)` steps to `E` itself (the argument then continues
  stepping in later steps).  Mirrors the runtime's eval rule; its official
  counterpart is exactly `MinimalStep.eval` (see `SmallStepSound.lean`). -/
  | eval_step {es : List Atom} {e : Atom}
      (h_shape : es = [.symbol "eval", e]) :
      HESmallStep space d fuel (.expression es) e
  /-- `HES_Chain`, source-progress case: while the source can step, the chain
  steps it in place. -/
  | chain_source {es : List Atom} {a a' : Atom} {v : String} {t : Atom}
      (h_shape : es = [.symbol "chain", a, .var v, t])
      (h_src : HESmallStep space d fuel a a') :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "chain", a', .var v, t])
  /-- `HES_Chain`, substitution case: when the source is quiescent, the chain
  substitutes it for the variable in the template (official
  `Bindings.applyDefault`, as in `MinimalStep.chain`). -/
  | chain_subst {es : List Atom} {a : Atom} {v : String} {t : Atom}
      (h_shape : es = [.symbol "chain", a, .var v, t])
      (h_quiescent : ¬ HECanSmallStep space d fuel a) :
      HESmallStep space d fuel (.expression es)
        ((Bindings.empty.assign v a).applyDefault t)
  /-- `function` source-progress case: while the body can step, the function
  steps it in place.  `return` is treated as an inert control sentinel, so
  this rule is the only way the wrapper makes progress before it unwraps. -/
  | function_source {es : List Atom} {body body' : Atom}
      (h_shape : es = [.symbol "function", body])
      (h_src : HESmallStep space d fuel body body') :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "function", body'])
  /-- `function` return case: a quiescent `(return x)` body unwraps to `x`
  literally, with no further evaluation of the payload at this surface step. -/
  | function_return {es : List Atom} {body ret : Atom}
      (h_shape : es = [.symbol "function", body])
      (h_quiescent : ¬ HECanSmallStep space d fuel body)
      (h_ret : body = .expression [.symbol "return", ret]) :
      HESmallStep space d fuel (.expression es) ret
  /-- `function` NoReturn case: a quiescent body that is not a `(return ...)`
  produces the spec-shaped `NoReturn` error. -/
  | function_no_return {es : List Atom} {body : Atom}
      (h_shape : es = [.symbol "function", body])
      (h_quiescent : ¬ HECanSmallStep space d fuel body)
      (h_not_return : ∀ ret, body ≠ .expression [.symbol "return", ret]) :
      HESmallStep space d fuel (.expression es)
        (Atom.error (.expression [.symbol "function", body]) (.symbol "NoReturn"))
  /-- `HES_EquationMatch`: a `(= lhs rhs)` equation in the space matches the
  expression; the successor is the freshened right-hand side under the query
  bindings — exactly the data `queryEquations` returns and the application
  `EvalSpec.lean`'s `equation_match` performs (with empty incoming
  bindings).  Relational: every matching equation contributes a successor. -/
  | equation_match {es : List Atom} {rhs : Atom} {qb : Bindings}
      (h_not_special : ¬ SpecialFormHead (.expression es))
      (h_not_grounded : HeadNotExecutable d (.expression es))
      (h_query : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
      (h_no_loop : qb.hasLoop = false) :
      HESmallStep space d fuel (.expression es) (qb.apply rhs fuel)
  /-- `HES_LetStar`, empty-bindings case: `(let* () body)` steps to the body. -/
  | letStar_empty {es : List Atom} {body : Atom}
      (h_shape : es = [.symbol "let*", .expression [], body]) :
      HESmallStep space d fuel (.expression es) body
  /-- `HES_LetStar`, unroll case: the first (well-formed) binding desugars to
  a `let` around the remaining `let*`. -/
  | letStar_unroll {es : List Atom} {pt vt body : Atom} {rest : List Atom}
      (h_shape : es = [.symbol "let*",
        .expression (.expression [pt, vt] :: rest), body]) :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "let", pt, vt,
          .expression [.symbol "let*", .expression rest, body]])
  /-- `HES_Let`, source-progress case: while the bound value can step, the
  `let` steps it in place. -/
  | let_source {es : List Atom} {pt v v' body : Atom}
      (h_shape : es = [.symbol "let", pt, v, body])
      (h_src : HESmallStep space d fuel v v') :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "let", pt, v', body])
  /-- `HES_Let`, substitution case: when the bound value is quiescent and the
  binder pattern matches it (official `simpleMatch`, empty seed), the `let`
  applies the match bindings to the body.  No match means no visible
  successor (evaluation to Empty is absorbed; the Empty-algebra doctrine). -/
  | let_subst {es : List Atom} {pt v body : Atom} {mb : Bindings}
      (h_shape : es = [.symbol "let", pt, v, body])
      (h_quiescent : ¬ HECanSmallStep space d fuel v)
      (h_match : simpleMatch pt v Bindings.empty fuel = some mb) :
      HESmallStep space d fuel (.expression es) (mb.applyDefault body)
  /-- `HES_Case`, scrutinee-progress case. -/
  | case_scrutinee {es : List Atom} {scrut scrut' branches : Atom}
      (h_shape : es = [.symbol "case", scrut, branches])
      (h_src : HESmallStep space d fuel scrut scrut') :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "case", scrut', branches])
  /-- `HES_Case`, branch-selection case: scrutinee quiescent; the first
  well-formed branch whose pattern matches wins (earlier well-formed
  branches must fail to match). -/
  | case_match {es : List Atom} {scrut : Atom} {branches : List Atom}
      {i : Nat} {pt t : Atom} {mb : Bindings}
      (h_shape : es = [.symbol "case", scrut, .expression branches])
      (h_quiescent : ¬ HECanSmallStep space d fuel scrut)
      (h_branch : branches[i]? = some (.expression [pt, t]))
      (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
      (h_earlier : ∀ j < i, ∀ pt' t',
        branches[j]? = some (.expression [pt', t']) →
        simpleMatch pt' scrut Bindings.empty fuel = none) :
      HESmallStep space d fuel (.expression es) (mb.applyDefault t)
  /-- `HES_Switch`, scrutinee-progress case: `switch` evaluates its
  scrutinee (upstream contract, split ratified 2026-06-10), so while the
  scrutinee can step, the switch steps it in place. -/
  | switch_scrutinee {es : List Atom} {scrut scrut' branches : Atom}
      (h_shape : es = [.symbol "switch", scrut, branches])
      (h_src : HESmallStep space d fuel scrut scrut') :
      HESmallStep space d fuel (.expression es)
        (.expression [.symbol "switch", scrut', branches])
  /-- `HES_Switch`, branch-selection case: scrutinee quiescent; first
  well-formed matching branch wins. -/
  | switch_match {es : List Atom} {scrut : Atom} {branches : List Atom}
      {i : Nat} {pt t : Atom} {mb : Bindings}
      (h_shape : es = [.symbol "switch", scrut, .expression branches])
      (h_quiescent : ¬ HECanSmallStep space d fuel scrut)
      (h_branch : branches[i]? = some (.expression [pt, t]))
      (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
      (h_earlier : ∀ j < i, ∀ pt' t',
        branches[j]? = some (.expression [pt', t']) →
        simpleMatch pt' scrut Bindings.empty fuel = none) :
      HESmallStep space d fuel (.expression es) (mb.applyDefault t)
  /-- `HES_SwitchMinimal`: structural match against the *raw* scrutinee;
  first well-formed matching branch wins. -/
  | switch_minimal_match {es : List Atom} {scrut : Atom}
      {branches : List Atom} {i : Nat} {pt t : Atom} {mb : Bindings}
      (h_shape : es = [.symbol "switch-minimal", scrut, .expression branches])
      (h_branch : branches[i]? = some (.expression [pt, t]))
      (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
      (h_earlier : ∀ j < i, ∀ pt' t',
        branches[j]? = some (.expression [pt', t']) →
        simpleMatch pt' scrut Bindings.empty fuel = none) :
      HESmallStep space d fuel (.expression es) (mb.applyDefault t)
  /-- `HES_LeftmostExprCongruence`: when the whole expression is neither a
  grounded redex nor an equation redex, the leftmost steppable element steps
  in place.  Earlier siblings are required quiescent via `HECanSmallStep`
  (positive polarity); `canStep_of_step` justifies reading that as
  "no step". -/
  | leftmost_congruence {pre : List Atom} {a a' : Atom} {post : List Atom}
      (h_not_special : ¬ SpecialFormHead (.expression (pre ++ a :: post)))
      (h_not_redex : ¬ GroundedRedex d (.expression (pre ++ a :: post)))
      (h_not_eq : ¬ EquationRedex space d fuel (.expression (pre ++ a :: post)))
      (h_pre : ∀ b ∈ pre, ¬ HECanSmallStep space d fuel b)
      (h_step : HESmallStep space d fuel a a') :
      HESmallStep space d fuel (.expression (pre ++ a :: post))
                               (.expression (pre ++ a' :: post))

/-! ## Soundness of the steppability predicate -/

/-- Every step witnesses steppability.  (Contrapositive: a
`¬ HECanSmallStep` side condition really excludes all steps.) -/
theorem canStep_of_step {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {a b : Atom} (h : HESmallStep space d fuel a b) :
    HECanSmallStep space d fuel a := by
  induction h with
  | @grounded_dispatch op args rs r bs h_not_special h_exec h_run h_mem =>
      exact .grounded h_not_special ⟨op, args, rs, r, bs, rfl, h_exec, h_run, h_mem⟩
  | @equation_match es rhs qb h_not_special h_not_grounded h_query h_no_loop =>
      exact .equation ⟨⟨es, rfl⟩, h_not_special, h_not_grounded,
        ⟨(rhs, qb), h_query, h_no_loop⟩⟩
  | eval_step h_shape => exact .eval_form h_shape
  | chain_source h_shape _ _ => exact .chain_form h_shape
  | chain_subst h_shape _ => exact .chain_form h_shape
  | function_source h_shape _ _ => exact .function_form h_shape
  | function_return h_shape _ _ => exact .function_form h_shape
  | function_no_return h_shape _ _ => exact .function_form h_shape
  | letStar_empty h_shape => exact .letStar_empty_form h_shape
  | letStar_unroll h_shape => exact .letStar_unroll_form h_shape
  | @let_source es pt v v' body h_shape h_src ih =>
      exact .let_source_form h_shape ih
  | @let_subst es pt v body mb h_shape h_q h_match =>
      exact .let_subst_form h_shape ⟨mb, h_match⟩
  | @case_scrutinee es scrut scrut' branches h_shape h_src ih =>
      exact .case_scrutinee_form h_shape ih
  | @case_match es scrut branches i pt t mb h_shape h_q h_branch h_match h_earlier =>
      exact .case_match_form h_shape ⟨i, pt, t, mb, h_branch, h_match, h_earlier⟩
  | @switch_scrutinee es scrut scrut' branches h_shape h_src ih =>
      exact .switch_scrutinee_form h_shape ih
  | @switch_match es scrut branches i pt t mb h_shape h_q h_branch h_match h_earlier =>
      exact .switch_match_form h_shape ⟨i, pt, t, mb, h_branch, h_match, h_earlier⟩
  | @switch_minimal_match es scrut branches i pt t mb h_shape h_branch h_match h_earlier =>
      exact .switch_minimal_form h_shape ⟨i, pt, t, mb, h_branch, h_match, h_earlier⟩
  | @leftmost_congruence pre a a' post h_not_special _ _ _ _ ih =>
      exact .element h_not_special
        (List.mem_append_right pre (List.mem_cons_self ..)) ih

/-- An atom that cannot step (by the steppability predicate) has no
successors. -/
theorem no_step_of_not_canStep {space : Space} {d : GroundedDispatch}
    {fuel : Nat} {a : Atom} (h : ¬ HECanSmallStep space d fuel a) :
    ∀ b, ¬ HESmallStep space d fuel a b :=
  fun _ hstep => h (canStep_of_step hstep)

/-! ## Totality: steppable atoms really step

The converse of `canStep_of_step`: if `HECanSmallStep` holds, an actual step
exists.  The proof finds the leftmost steppable element classically and
recurses on atom size. -/

private theorem split_first_canStep (space : Space) (d : GroundedDispatch)
    (fuel : Nat) :
    ∀ (es : List Atom), (∃ e ∈ es, HECanSmallStep space d fuel e) →
      ∃ pre x post, es = pre ++ x :: post ∧ HECanSmallStep space d fuel x ∧
        ∀ b ∈ pre, ¬ HECanSmallStep space d fuel b
  | [], h => absurd h (by simp)
  | e :: es, h => by
      by_cases he : HECanSmallStep space d fuel e
      · exact ⟨[], e, es, rfl, he, by simp⟩
      · have h' : ∃ x ∈ es, HECanSmallStep space d fuel x := by
          obtain ⟨x, hx_mem, hx⟩ := h
          rcases List.mem_cons.mp hx_mem with rfl | hx_mem'
          · exact absurd hx he
          · exact ⟨x, hx_mem', hx⟩
        obtain ⟨pre, x, post, heq, hx, hpre⟩ :=
          split_first_canStep space d fuel es h'
        refine ⟨e :: pre, x, post, by simp [heq], hx, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact he
        · exact hpre b hb'

/-- Steppable atoms have at least one successor: the HE small-step relation
is total on `HECanSmallStep`. -/
theorem exists_step_of_canStep {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    (a : Atom) → HECanSmallStep space d fuel a →
      ∃ b, HESmallStep space d fuel a b
  | a, h => by
      by_cases hsf : SpecialFormHead a
      · -- special-form heads: only the modeled forms can be steppable, and
        -- both always step
        cases h with
        | grounded h_ns _ => exact absurd hsf h_ns
        | equation he' => exact absurd hsf he'.2.1
        | eval_form h_shape => exact ⟨_, HESmallStep.eval_step h_shape⟩
        | @chain_form es a v t h_shape =>
            by_cases hca : HECanSmallStep space d fuel a
            · obtain ⟨a', ha'⟩ := exists_step_of_canStep a hca
              exact ⟨_, HESmallStep.chain_source h_shape ha'⟩
            · exact ⟨_, HESmallStep.chain_subst h_shape hca⟩
        | @function_form es body h_shape =>
            by_cases hcb : HECanSmallStep space d fuel body
            · obtain ⟨body', hb'⟩ := exists_step_of_canStep body hcb
              exact ⟨_, HESmallStep.function_source h_shape hb'⟩
            · by_cases hret : ∃ ret, body = .expression [.symbol "return", ret]
              · obtain ⟨ret, hret_eq⟩ := hret
                exact ⟨_, HESmallStep.function_return h_shape hcb hret_eq⟩
              · exact ⟨_, HESmallStep.function_no_return h_shape hcb (by
                  intro ret h_eq
                  exact hret ⟨ret, h_eq⟩)⟩
        | letStar_empty_form h_shape =>
            exact ⟨_, HESmallStep.letStar_empty h_shape⟩
        | letStar_unroll_form h_shape =>
            exact ⟨_, HESmallStep.letStar_unroll h_shape⟩
        | @let_source_form es pt v body h_shape h_can =>
            obtain ⟨v', hv'⟩ := exists_step_of_canStep v h_can
            exact ⟨_, HESmallStep.let_source h_shape hv'⟩
        | @let_subst_form es pt v body h_shape h_match =>
            by_cases hcv : HECanSmallStep space d fuel v
            · obtain ⟨v', hv'⟩ := exists_step_of_canStep v hcv
              exact ⟨_, HESmallStep.let_source h_shape hv'⟩
            · obtain ⟨mb, hm⟩ := h_match
              exact ⟨_, HESmallStep.let_subst h_shape hcv hm⟩
        | @case_scrutinee_form es scrut branches h_shape h_can =>
            obtain ⟨s', hs'⟩ := exists_step_of_canStep scrut h_can
            exact ⟨_, HESmallStep.case_scrutinee h_shape hs'⟩
        | @case_match_form es scrut branches h_shape h_can =>
            by_cases hcs : HECanSmallStep space d fuel scrut
            · obtain ⟨s', hs'⟩ := exists_step_of_canStep scrut hcs
              exact ⟨_, HESmallStep.case_scrutinee h_shape hs'⟩
            · obtain ⟨i, pt, t, mb, hb, hm, hearlier⟩ := h_can
              exact ⟨_, HESmallStep.case_match h_shape hcs hb hm hearlier⟩
        | @switch_scrutinee_form es scrut branches h_shape h_can =>
            obtain ⟨s', hs'⟩ := exists_step_of_canStep scrut h_can
            exact ⟨_, HESmallStep.switch_scrutinee h_shape hs'⟩
        | @switch_match_form es scrut branches h_shape h_can =>
            by_cases hcs : HECanSmallStep space d fuel scrut
            · obtain ⟨s', hs'⟩ := exists_step_of_canStep scrut hcs
              exact ⟨_, HESmallStep.switch_scrutinee h_shape hs'⟩
            · obtain ⟨i, pt, t, mb, hb, hm, hearlier⟩ := h_can
              exact ⟨_, HESmallStep.switch_match h_shape hcs hb hm hearlier⟩
        | @switch_minimal_form es scrut branches h_shape h_can =>
            obtain ⟨i, pt, t, mb, hb, hm, hearlier⟩ := h_can
            exact ⟨_, HESmallStep.switch_minimal_match h_shape hb hm hearlier⟩
        | element h_ns _ _ => exact absurd hsf h_ns
      · by_cases hg : GroundedRedex d a
        · obtain ⟨op, args, rs, r, bs, ha, h_exec, h_run, h_mem⟩ := hg
          exact ⟨r, ha ▸ HESmallStep.grounded_dispatch (ha ▸ hsf) h_exec h_run h_mem⟩
        · by_cases he : EquationRedex space d fuel a
          · obtain ⟨⟨es, rfl⟩, h_ns, h_not_grounded, ⟨rhs, qb⟩, h_mem, h_loop⟩ := he
            exact ⟨qb.apply rhs fuel,
                   HESmallStep.equation_match h_ns h_not_grounded h_mem h_loop⟩
          · cases h with
            | grounded _ hg' => exact absurd hg' hg
            | equation he' => exact absurd he' he
            | eval_form h_shape =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | chain_form h_shape =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | function_form h_shape =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | letStar_empty_form h_shape =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | letStar_unroll_form h_shape =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | let_source_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | let_subst_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | case_scrutinee_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | case_match_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | switch_scrutinee_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | switch_match_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | switch_minimal_form h_shape _ =>
                exact absurd (by simp [SpecialFormHead, h_shape]) hsf
            | @element es e h_ns h_mem h_e =>
                obtain ⟨pre, x, post, heq, hx, hpre⟩ :=
                  split_first_canStep space d fuel es ⟨e, h_mem, h_e⟩
                have hx_mem : x ∈ es := heq ▸ List.mem_append_right pre
                  (List.mem_cons_self ..)
                obtain ⟨x', hx'⟩ := exists_step_of_canStep x hx
                subst heq
                exact ⟨.expression (pre ++ x' :: post),
                       .leftmost_congruence hsf hg he hpre hx'⟩
  termination_by a _ => sizeOf a
  decreasing_by
  · -- chain source recursion
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- let source recursion (source-form)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- function source recursion
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- let source recursion (subst-form fallback)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- case scrutinee recursion (scrutinee-form)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- case scrutinee recursion (match-form fallback)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- switch scrutinee recursion (scrutinee-form)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- switch scrutinee recursion (match-form fallback)
    subst h_shape
    simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec,
      List.nil.sizeOf_spec]
    omega
  · -- congruence recursion: a list element is smaller than the expression
    have h1 : sizeOf x < sizeOf es := List.sizeOf_lt_of_mem hx_mem
    have h2 : sizeOf (Atom.expression es) = 1 + sizeOf es := by
      simp [Atom.expression.sizeOf_spec]
    omega

/-! ## The OSLF reduction span and modal layer -/

/-- The OSLF reduction span over `HESmallStep`: edges are witnessed steps. -/
def heSmallStepSpan (space : Space) (d : GroundedDispatch) (fuel : Nat) :
    ReductionSpan Atom where
  Edge := { p : Atom × Atom // HESmallStep space d fuel p.1 p.2 }
  source := fun e => e.val.1
  target := fun e => e.val.2

/-- `◇⊤` is exactly "some successor exists" — the runtime's
`lts:he:is-can-step`. -/
theorem diamond_top_iff_exists_step (space : Space) (d : GroundedDispatch)
    (fuel : Nat) (a : Atom) :
    derivedDiamond (heSmallStepSpan space d fuel) (fun _ => True) a ↔
      ∃ b, HESmallStep space d fuel a b := by
  constructor
  · rintro ⟨e, h_src, -⟩
    exact ⟨e.val.2, h_src ▸ e.property⟩
  · rintro ⟨b, h⟩
    exact ⟨⟨(a, b), h⟩, rfl, trivial⟩

/-- Small-step normal form: no successor exists. -/
def SmallStepNormalForm (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (a : Atom) : Prop :=
  ∀ b, ¬ HESmallStep space d fuel a b

theorem normalForm_iff_not_diamond_top (space : Space) (d : GroundedDispatch)
    (fuel : Nat) (a : Atom) :
    SmallStepNormalForm space d fuel a ↔
      ¬ derivedDiamond (heSmallStepSpan space d fuel) (fun _ => True) a := by
  rw [diamond_top_iff_exists_step]
  exact ⟨fun h ⟨b, hb⟩ => h b hb, fun h b hb => h ⟨b, hb⟩⟩

/-! ### Successor box vs.\ predecessor box

The runtime's `lts:he:box` quantifies over *successors* (`successorBox`
below).  OSLF's `derivedBox` quantifies over *predecessors* — it is the
Galois adjoint of `derivedDiamond` (`◇ ⊣ ⊟`, the standard future-diamond /
past-box adjunction).  The successor box is instead the De Morgan dual of
`derivedDiamond`.  Both relationships are stated; conflating them is a
category error this file exists to prevent. -/

/-- Successor box: every one-step successor satisfies `φ` (vacuously true at
normal forms).  This is the runtime's `lts:he:box`. -/
def successorBox (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (φ : Atom → Prop) (a : Atom) : Prop :=
  ∀ b, HESmallStep space d fuel a b → φ b

/-- De Morgan: the successor box is the dual of the derived diamond.  This is
the law the runtime installs as a self-test
(`box φ == not (diamond (not φ))`). -/
theorem successorBox_iff_not_diamond_not (space : Space)
    (d : GroundedDispatch) (fuel : Nat) (φ : Atom → Prop) (a : Atom) :
    successorBox space d fuel φ a ↔
      ¬ derivedDiamond (heSmallStepSpan space d fuel) (fun x => ¬ φ x) a := by
  constructor
  · rintro h ⟨e, h_src, h_not⟩
    exact h_not (h e.val.2 (h_src ▸ e.property))
  · intro h b hb
    by_contra h_not
    exact h ⟨⟨(a, b), hb⟩, rfl, h_not⟩

/-- `□⊥` (successor box of falsity) is exactly normal form — the runtime's
`is-normal-form == box(const-false)` self-test. -/
theorem normalForm_iff_successorBox_false (space : Space)
    (d : GroundedDispatch) (fuel : Nat) (a : Atom) :
    SmallStepNormalForm space d fuel a ↔
      successorBox space d fuel (fun _ => False) a :=
  Iff.rfl

/-- The Galois connection `◇ ⊣ □` for the HE small-step span, inherited from
the generic OSLF derivation.  (`derivedBox` here is the *predecessor* box;
see the section note above.) -/
theorem heSmallStep_galois (space : Space) (d : GroundedDispatch)
    (fuel : Nat) :
    GaloisConnection (derivedDiamond (heSmallStepSpan space d fuel))
      (derivedBox (heSmallStepSpan space d fuel)) :=
  derived_galois _

/-! ## Concrete witnesses (positive and negative)

A toy dispatch oracle with integer addition and a one-equation space,
mirroring the runtime witnesses in `tests/test_step_rules.metta`. -/

private def plusDispatch : GroundedDispatch where
  isExecutable := fun a =>
    match a with
    | .symbol "+" => true
    | _ => false
  execute := fun op args =>
    match op, args with
    | .symbol "+", [.grounded (.int m), .grounded (.int n)] =>
        .ok [(.grounded (.int (m + n)), default)]
    | _, _ => .noReduce

/-- `(= (f $x) (g $x))` -/
private def eqSpace : Space :=
  Space.ofList [.expression [.symbol "=",
    .expression [.symbol "f", .var "x"],
    .expression [.symbol "g", .var "x"]]]

/-- Positive: `(+ 2 3) → 5` by grounded dispatch (over the empty space). -/
example : HESmallStep Space.empty plusDispatch 100
    (.expression [.symbol "+", .grounded (.int 2), .grounded (.int 3)])
    (.grounded (.int 5)) :=
  .grounded_dispatch (op := .symbol "+") (bs := default)
    (by simp [SpecialFormHead]) rfl rfl (by simp)

/-- Positive: `(f 5)` is an equation redex in `eqSpace` (decidably), so it
genuinely steps — the runtime witness `(f 5) → (g 5)` in existential form. -/
example : ∃ b, HESmallStep eqSpace plusDispatch 100
    (.expression [.symbol "f", .grounded (.int 5)]) b :=
  exists_step_of_canStep _ (.equation (by
    refine ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩
    · simp [SpecialFormHead]
    · simp [HeadNotExecutable, plusDispatch]
    · decide))

/-- Negative: with an empty space, nothing is an equation redex. -/
example (d : GroundedDispatch) (fuel : Nat) (a : Atom) :
    ¬ EquationRedex Space.empty d fuel a := by
  rintro ⟨⟨es, rfl⟩, -, -, p, h_mem, -⟩
  simp [queryEquations, Space.empty] at h_mem

/-- Bare symbols cannot step (no constructor applies). -/
theorem symbol_normalForm (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (s : String) : SmallStepNormalForm space d fuel (.symbol s) := by
  intro b h
  cases h

/-- Bare grounded values cannot step. -/
theorem grounded_normalForm (space : Space) (d : GroundedDispatch)
    (fuel : Nat) (g : GroundedValue) :
    SmallStepNormalForm space d fuel (.grounded g) := by
  intro b h
  cases h

/-- Symbols are not steppable. -/
theorem not_canStep_symbol (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (s : String) : ¬ HECanSmallStep space d fuel (.symbol s) := by
  intro h
  cases h with
  | grounded _ hg => obtain ⟨_, _, _, _, _, h, _⟩ := hg; cases h
  | equation he => obtain ⟨⟨_, h⟩, -, -, -⟩ := he; cases h

/-- Grounded values are not steppable. -/
theorem not_canStep_grounded (space : Space) (d : GroundedDispatch)
    (fuel : Nat) (g : GroundedValue) :
    ¬ HECanSmallStep space d fuel (.grounded g) := by
  intro h
  cases h with
  | grounded _ hg => obtain ⟨_, _, _, _, _, h, _⟩ := hg; cases h
  | equation he => obtain ⟨⟨_, h⟩, -, -, -⟩ := he; cases h

/-- Positive: the congruence witness `(+ 1 (+ 2 3)) → (+ 1 5)` over the
empty space.  The outer expression is neither a grounded redex (the second
argument is unevaluated) nor an equation redex (empty space); the elements
left of the inner redex are quiescent; the inner grounded step lifts. -/
example : HESmallStep Space.empty plusDispatch 100
    (.expression [.symbol "+", .grounded (.int 1),
      .expression [.symbol "+", .grounded (.int 2), .grounded (.int 3)]])
    (.expression [.symbol "+", .grounded (.int 1), .grounded (.int 5)]) := by
  have h_inner : HESmallStep Space.empty plusDispatch 100
      (.expression [.symbol "+", .grounded (.int 2), .grounded (.int 3)])
      (.grounded (.int 5)) :=
    .grounded_dispatch (op := .symbol "+") (bs := default)
      (by simp [SpecialFormHead]) rfl rfl (by simp)
  have h := HESmallStep.leftmost_congruence
    (space := Space.empty) (d := plusDispatch) (fuel := 100)
    (pre := [.symbol "+", .grounded (.int 1)])
    (post := [])
    (a := .expression [.symbol "+", .grounded (.int 2), .grounded (.int 3)])
    (a' := .grounded (.int 5))
    (h_not_special := by simp [SpecialFormHead])
    (h_not_redex := by
      rintro ⟨op, args, rs, r, bs, h_eq, h_exec, h_run, h_mem⟩
      obtain ⟨rfl, rfl⟩ : op = .symbol "+" ∧
          args = [.grounded (.int 1),
            .expression [.symbol "+", .grounded (.int 2), .grounded (.int 3)]] := by
        injection h_eq with h_list
        injection h_list with h1 h2
        exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
      simp [plusDispatch] at h_run)
    (h_not_eq := by
      rintro ⟨⟨es, h_eq⟩, -, -, p, h_mem, -⟩
      rw [h_eq] at h_mem
      simp [queryEquations, Space.empty] at h_mem)
    (h_pre := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact not_canStep_symbol _ _ _ _
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact not_canStep_grounded _ _ _ _
      · cases hb'')
    (h_step := h_inner)
  exact h

/-- Negative: an inert application is not steppable over the empty space —
the head is not executable, no equation matches, every element quiescent. -/
theorem inert_application_not_canStep :
    ¬ HECanSmallStep Space.empty plusDispatch 100
      (.expression [.symbol "foo", .grounded (.int 1)]) := by
  intro h
  cases h with
  | grounded _ hg =>
      obtain ⟨op, args, rs, r, bs, h_eq, h_exec, h_run, h_mem⟩ := hg
      injection h_eq with h_list
      injection h_list with h1 h2
      subst h1
      simp [plusDispatch] at h_exec
  | equation he =>
      obtain ⟨-, -, -, p, h_mem, -⟩ := he
      simp [queryEquations, Space.empty] at h_mem
  | eval_form h_shape => simp at h_shape
  | chain_form h_shape => simp at h_shape
  | function_form h_shape => simp at h_shape
  | letStar_empty_form h_shape => simp at h_shape
  | letStar_unroll_form h_shape => simp at h_shape
  | let_source_form h_shape _ => simp at h_shape
  | let_subst_form h_shape _ => simp at h_shape
  | case_scrutinee_form h_shape _ => simp at h_shape
  | case_match_form h_shape _ => simp at h_shape
  | switch_scrutinee_form h_shape _ => simp at h_shape
  | switch_match_form h_shape _ => simp at h_shape
  | switch_minimal_form h_shape _ => simp at h_shape
  | element _ h_mem h_e =>
      rcases List.mem_cons.mp h_mem with rfl | h'
      · exact not_canStep_symbol _ _ _ _ h_e
      rcases List.mem_cons.mp h' with rfl | h''
      · exact not_canStep_grounded _ _ _ _ h_e
      · cases h''

/-- Negative: a fully-reduced inert application is a small-step normal form
(via the soundness lemma: not steppable, hence no successors). -/
theorem inert_application_normalForm :
    SmallStepNormalForm Space.empty plusDispatch 100
      (.expression [.symbol "foo", .grounded (.int 1)]) :=
  no_step_of_not_canStep inert_application_not_canStep

end Mettapedia.Languages.MeTTa.HE
