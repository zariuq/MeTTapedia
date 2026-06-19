import Mettapedia.Languages.MeTTa.HE.SmallStepContext
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence
import Mettapedia.Languages.MeTTa.HE.SmallStepSound

/-!
# Master Absorption, Step S1: Atom-Level Tuple Transport

The fragment master theorem's congruence workhorse (design note S1): an
official tuple derivation of `(pre ++ x' :: post)` transports to
`(pre ++ x :: post)` **at the result-atom level** (existential result
bindings), given

* an atom-level result-preserving substitution for the active position
  (exactly the fragment master theorem's induction hypothesis), and
* Q-domain membership for the spectator elements (`pre` and `post`),
  with `post` additionally carrying the T6/T7 shape conditions.

Why this works (and why pair-exact transport — `interpretTuple_swap` —
is not enough): the active element's result *bindings* may shift (T10:
equation steps grow the official bindings thread), and the `post`
elements officially evaluate under those shifted bindings.  Q-uniformity
(`selfEval_of_quiescent`, any incoming bindings) rebuilds the source's
post-segment under the shifted thread, and Q-uniqueness
(`selfEval_unique`, S0) pins the successor's spectator sub-derivations so
the result atoms agree.  We state only what we prove.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- **S1 (atom-level tuple transport).** -/
theorem tuple_swap_atom {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {x x' : Atom} {b : Bindings}
    (h_sub : ∀ (r' : ResultPair),
      EvalAtom space d x' Atom.undefinedType b r' →
      ∃ rb, EvalAtom space d x Atom.undefinedType b (r'.1, rb)) :
    ∀ (pre : List Atom) {post : List Atom} {r : ResultPair}
      {l : List Atom}, l = pre ++ x' :: post →
      (∀ e ∈ pre, SelfEvalQuiescent space d fuel e) →
      (∀ e ∈ post, SelfEvalQuiescent space d fuel e) →
      (∀ es', post.getLast? = some (Atom.expression es') → False) →
      (∀ e ∈ post, e ≠ Atom.symbol "Error") →
      InterpretTuple space d (.expression l) b r →
      ∃ rb, InterpretTuple space d (.expression (pre ++ x :: post)) b (r.1, rb)
  | [], post, r, l, h_eq, h_pre, h_post, h_last, h_nes, h => by
      cases h with
      | singleton a _ _ h_eval =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          obtain ⟨rb, h_ev⟩ := h_sub r h_eval
          exact ⟨rb, InterpretTuple.singleton x b (r.1, rb) h_ev⟩
      | @head_error _ _ _ _ h_ne h_ev h_isErr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          obtain ⟨rb, h_ev'⟩ := h_sub _ h_ev
          exact ⟨rb, InterpretTuple.head_error x post b (r.1, rb) h_ne
            h_ev' h_isErr⟩
      | @tail_error hd tl _ hr tr h_ne h_ev h_hok h_tail h_terr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          -- the post-tail of Q-domain elements cannot produce Empty/Error
          exfalso
          cases post with
          | nil => exact h_ne rfl
          | cons p ps =>
              cases ps with
              | nil =>
                  cases h_tail with
                  | @singleton _ _ _ h_ev_p =>
                      have hp := selfEval_unique p (h_post p (by simp)) h_ev_p
                      have h_ok := (h_post p (by simp)).not_empty_or_error
                      rw [hp] at h_terr
                      simp [h_terr] at h_ok
                  | @head_error _ _ _ _ h_ne' _ _ => exact h_ne' rfl
                  | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact h_ne' rfl
                  | @success _ _ _ _ _ h_ne' _ _ _ _ => exact h_ne' rfl
              | cons q qs =>
                  have h_tr := tuple_unique_of p q qs h_post
                    (fun e he => selfEval_unique e (h_post e he))
                    h_last h_nes h_tail
                  rw [h_tr] at h_terr
                  have h_ok := isEmptyOrError_expr_false (q :: qs)
                    (h_nes p (by simp))
                  simp [h_terr] at h_ok
      | @success hd tl _ hr tr h_ne h_ev h_hok h_tl h_tok =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          obtain ⟨rb, h_ev'⟩ := h_sub _ h_ev
          cases post with
          | nil => exact absurd rfl h_ne
          | cons p ps =>
              cases ps with
              | nil =>
                  cases h_tl with
                  | @singleton _ _ _ h_ev_p =>
                      have hp := selfEval_unique p (h_post p (by simp)) h_ev_p
                      subst hp
                      refine ⟨rb, ?_⟩
                      have h_p_src : EvalAtom space d p Atom.undefinedType rb
                          (p, rb) :=
                        selfEval_of_quiescent p (h_post p (by simp)) rb
                      have h_comb := InterpretTuple.success x [p] b
                        (hr.1, rb) (p, rb) (by simp) h_ev' h_hok
                        (InterpretTuple.singleton p rb (p, rb) h_p_src)
                        ((h_post p (by simp)).not_empty_or_error)
                      simpa using h_comb
                  | @head_error _ _ _ _ h_ne' _ _ => exact absurd rfl h_ne'
                  | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
                  | @success _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
              | cons q qs =>
                  have h_tr := tuple_unique_of p q qs h_post
                    (fun e he => selfEval_unique e (h_post e he))
                    h_last h_nes h_tl
                  subst h_tr
                  refine ⟨rb, ?_⟩
                  have h_tail_src : InterpretTuple space d
                      (.expression (p :: q :: qs)) rb
                      (.expression (p :: q :: qs), rb) :=
                    tuple_self p q qs rb
                      (fun e he b' => selfEval_of_quiescent e (h_post e he) b')
                      (fun e he => (h_post e he).not_empty_or_error)
                      h_last h_nes
                  have h_comb := InterpretTuple.success x (p :: q :: qs) b
                    (hr.1, rb) (.expression (p :: q :: qs), rb)
                    (by simp) h_ev' h_hok h_tail_src
                    (isEmptyOrError_expr_false (q :: qs) (h_nes p (by simp)))
                  simpa using h_comb
  | p :: ps, post, r, l, h_eq, h_pre, h_post, h_last, h_nes, h => by
      cases h with
      | singleton a _ _ h_eval =>
          exfalso
          injection h_eq.symm with h1 h2
          exact absurd h2.symm (by simp)
      | @head_error hd tl _ hr h_ne h_ev h_isErr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exfalso
          have hp := selfEval_unique p (h_pre p (by simp)) h_ev
          have h_ok := (h_pre p (by simp)).not_empty_or_error
          rw [hp] at h_isErr
          simp [h_isErr] at h_ok
      | @tail_error hd tl _ hr tr h_ne h_ev h_hok h_tail h_terr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          have hp := selfEval_unique p (h_pre p (by simp)) h_ev
          subst hp
          obtain ⟨rb, h_tail'⟩ := tuple_swap_atom h_sub ps rfl
            (fun e he => h_pre e (List.mem_cons_of_mem p he))
            h_post h_last h_nes h_tail
          exact ⟨rb, InterpretTuple.tail_error p (ps ++ x :: post) b
            (p, b) (r.1, rb) (by simp)
            (selfEval_of_quiescent p (h_pre p (by simp)) b)
            ((h_pre p (by simp)).not_empty_or_error)
            h_tail' h_terr⟩
      | @success hd tl _ hr tr h_ne h_ev h_hok h_tl h_tok =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          have hp := selfEval_unique p (h_pre p (by simp)) h_ev
          subst hp
          obtain ⟨rb, h_tl'⟩ := tuple_swap_atom h_sub ps rfl
            (fun e he => h_pre e (List.mem_cons_of_mem p he))
            h_post h_last h_nes h_tl
          refine ⟨rb, ?_⟩
          have h_comb := InterpretTuple.success p (ps ++ x :: post) b
            (p, b) (tr.1, rb) (by simp)
            (selfEval_of_quiescent p (h_pre p (by simp)) b)
            ((h_pre p (by simp)).not_empty_or_error)
            h_tl' h_tok
          simpa using h_comb

/-- **Tuple-result trichotomy**: a tuple derivation whose head is a
Q-domain element produces Empty, an Error-shaped atom, or an expression
keeping that head.  (The head-error arm is impossible: by S0 the head
evaluates to itself, and Q-domain atoms are not Empty/Error.) -/
theorem tuple_result_shape {space : Space} {d : GroundedDispatch}
    {fuel : Nat} {p : Atom} {tl : List Atom} {b : Bindings} {r : ResultPair}
    (h_p : SelfEvalQuiescent space d fuel p)
    (h_tl : tl ≠ [])
    (h : InterpretTuple space d (.expression (p :: tl)) b r) :
    r.1 = Atom.empty ∨ isErrorAtom r.1 = true ∨
      ∃ tailAtoms, r.1 = .expression (p :: tailAtoms) := by
  cases h with
  | singleton _ _ _ h_eval => exact absurd rfl h_tl
  | @head_error _ _ _ _ h_ne h_ev h_isErr =>
      have hp := selfEval_unique p h_p h_ev
      have h_ok := h_p.not_empty_or_error
      rw [hp] at h_isErr
      simp [h_isErr] at h_ok
  | @tail_error _ _ _ hr _ h_ne h_ev h_hok h_tail h_terr =>
      simp only [isEmptyOrError, Bool.or_eq_true] at h_terr
      rcases h_terr with h' | h'
      · exact Or.inl (by simpa [isEmptyAtom] using h')
      · exact Or.inr (Or.inl h')
  | @success _ _ _ hr tr h_ne h_ev h_hok h_tl h_tok =>
      have hp := selfEval_unique p h_p h_ev
      rw [hp]
      exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- `MettaCall` inertness for symbol atoms with no matching equations. -/
theorem mettaCall_symbol_inert {space : Space} {d : GroundedDispatch}
    {sym : String} {t : Atom} {b : Bindings} {r : ResultPair}
    (h_no_eqs : ∀ f, queryEquations space (.symbol sym) f = [])
    (h : MettaCall space d (.symbol sym) t b r) :
    r = (.symbol sym, b) := by
  cases h with
  | error_passthrough _ _ _ _ => rfl
  | unify_success_raw => simp_all
  | unify_no_match_raw => simp_all
  | unify_bad_arity => simp_all
  | switch_minimal_result => simp_all
  | switch_minimal_bad_shape => simp_all
  | no_match _ _ _ _ _ _ _ => rfl
  | grounded_ok => simp_all
  | grounded_runtime_error => simp_all
  | grounded_no_reduce => simp_all
  | grounded_incorrect_arg => simp_all
  | grounded_empty_results => simp_all
  | equation_match => simp_all
  | empty_results => simp_all

/-- **S2 (EvalAtom-level atom transport, non-head active position).**
On the constructor-headed untyped fragment, any official evaluation of
the successor expression transports to the source expression at the
result-atom level.  The constructor-like head (`h_head_*`) makes the
post-tuple `MettaCall` inert on both sides regardless of the evaluated
form (via the tuple-result trichotomy), which is what closes T10 one
level up from S1. -/
theorem evalAtom_swap_atom {space : Space} {d : GroundedDispatch}
    {fuel : Nat} {x x' : Atom} {b : Bindings}
    (h_sub : ∀ (r' : ResultPair),
      EvalAtom space d x' Atom.undefinedType b r' →
      ∃ rb, EvalAtom space d x Atom.undefinedType b (r'.1, rb))
    (p : Atom) (ps : List Atom) {post : List Atom}
    {r : ResultPair}
    (h_pre : ∀ e ∈ p :: ps, SelfEvalQuiescent space d fuel e)
    (h_post : ∀ e ∈ post, SelfEvalQuiescent space d fuel e)
    (h_post_last : ∀ es', post.getLast? = some (Atom.expression es') → False)
    (h_post_nes : ∀ e ∈ post, e ≠ Atom.symbol "Error")
    (h_head_nes : p ≠ Atom.symbol "Error")
    (h_head_untyped : getAtomTypes space p = [Atom.undefinedType])
    (h_head_not_exec : d.isExecutable p = false)
    (h_head_not_unify : p ≠ .symbol "unify")
    (h_head_not_switch : p ≠ .symbol "switch-minimal")
    (h_head_no_eqs : ∀ (es : List Atom) (f : Nat),
      queryEquations space (.expression (p :: es)) f = [])
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h : EvalAtom space d (.expression (p :: ps ++ x' :: post))
      Atom.undefinedType b r) :
    ∃ rb, EvalAtom space d (.expression (p :: ps ++ x :: post))
      Atom.undefinedType b (r.1, rb) := by
  have h_src_ok : isEmptyOrError (Atom.expression (p :: ps ++ x :: post)) = false :=
    isEmptyOrError_expr_false _ h_head_nes
  have h_succ_ok : isEmptyOrError (Atom.expression (p :: ps ++ x' :: post)) = false :=
    isEmptyOrError_expr_false _ h_head_nes
  cases h with
  | empty_or_error _ _ _ h' =>
      exact absurd h' (by rw [h_succ_ok]; simp)
  | type_pass _ _ _ _ h_np =>
      exact absurd h_np (by
        simp [getMetaType, Atom.undefinedType, Atom.atomType,
          Atom.expressionType, Atom.variableType])
  | @type_cast _ _ _ _ fuel' h_ne h_np h_branch h_result =>
      rcases h_branch with h' | h' | h'
      · simp [getMetaType, Atom.symbolType, Atom.expressionType] at h'
      · simp [getMetaType, Atom.groundedType, Atom.expressionType] at h'
      · simp [Atom.unit] at h'
  | interpret_success _ _ _ _ _ _ h_expr h_not_unit h_interp h_not_error =>
      cases h_interp with
      | function_path => simp_all [isFunctionType, Atom.undefinedType]
      | op_type_error => simp_all [isFunctionType, Atom.undefinedType]
      | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc =>
          obtain ⟨rb1, h_src_tuple⟩ := tuple_swap_atom h_sub (p :: ps) rfl
            h_pre h_post h_post_last h_post_nes h_tuple
          have h_shape_A := tuple_result_shape (h_pre p (by simp))
            (by simp) h_tuple
          have h_r : r = (tupleResult.1, tupleResult.2) := by
            rcases h_shape_A with hA | hA | ⟨ta, hA⟩
            · rw [hA] at h_mc ⊢
              exact mettaCall_symbol_inert
                (by simpa [Atom.empty] using h_empty_no_eqs) h_mc
            · cases h_mc with
              | error_passthrough _ _ _ _ => rfl
              | unify_success_raw => simp_all
              | unify_no_match_raw => simp_all
              | unify_bad_arity => simp_all
              | switch_minimal_result => simp_all
              | switch_minimal_bad_shape => simp_all
              | no_match _ _ _ _ _ _ _ => rfl
              | grounded_ok => simp_all
              | grounded_runtime_error => simp_all
              | grounded_no_reduce => simp_all
              | grounded_incorrect_arg => simp_all
              | grounded_empty_results => simp_all
              | equation_match => simp_all
              | empty_results => simp_all
            · rw [hA] at h_mc ⊢
              exact mettaCall_untyped_inert
                (by
                  unfold HeadNotExecutable
                  exact ⟨h_head_not_exec, h_head_not_unify, h_head_not_switch⟩)
                (h_head_no_eqs ta) h_mc
          subst h_r
          have h_src_call : MettaCall space d tupleResult.1
              Atom.undefinedType rb1 (tupleResult.1, rb1) := by
            rcases h_shape_A with hA | hA | ⟨ta, hA⟩
            · rw [hA]
              exact MettaCall.no_match _ _ _ fuel rfl
                (by simp [Atom.empty]) (by
                  simpa [Atom.empty] using h_empty_no_eqs fuel)
            · exact MettaCall.error_passthrough _ _ _ hA
            · rw [hA]
              exact MettaCall.no_match _ _ _ fuel
                (isErrorAtom_expr_false ta h_head_nes)
                ⟨h_head_not_exec, h_head_not_unify, h_head_not_switch⟩
                (h_head_no_eqs ta fuel)
          by_cases hAerr : isErrorAtom tupleResult.1 = true
          · exact ⟨rb1, EvalAtom.interpret_error _ _ _ _ h_src_ok
              (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
                Atom.expressionType, Atom.variableType])
              rfl
              (by intro h_unit; simp [Atom.unit] at h_unit)
              (InterpretExpression.tuple_path _ _ _
                (tupleResult.1, rb1) (tupleResult.1, rb1)
                ⟨Atom.undefinedType, by simp [h_head_untyped], Or.inr rfl⟩
                h_src_tuple h_src_call)
              hAerr⟩
          · exact ⟨rb1, EvalAtom.interpret_success _ _ _ _ h_src_ok
              (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
                Atom.expressionType, Atom.variableType])
              rfl
              (by intro h_unit; simp [Atom.unit] at h_unit)
              (InterpretExpression.tuple_path _ _ _
                (tupleResult.1, rb1) (tupleResult.1, rb1)
                ⟨Atom.undefinedType, by simp [h_head_untyped], Or.inr rfl⟩
                h_src_tuple h_src_call)
              (by simpa using hAerr)⟩
  | interpret_error _ _ _ _ _ _ h_expr h_not_unit h_interp h_is_error =>
      cases h_interp with
      | function_path => simp_all [isFunctionType, Atom.undefinedType]
      | op_type_error => simp_all [isFunctionType, Atom.undefinedType]
      | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc =>
          obtain ⟨rb1, h_src_tuple⟩ := tuple_swap_atom h_sub (p :: ps) rfl
            h_pre h_post h_post_last h_post_nes h_tuple
          have h_shape_A := tuple_result_shape (h_pre p (by simp))
            (by simp) h_tuple
          have h_r : r = (tupleResult.1, tupleResult.2) := by
            rcases h_shape_A with hA | hA | ⟨ta, hA⟩
            · rw [hA] at h_mc ⊢
              exact mettaCall_symbol_inert
                (by simpa [Atom.empty] using h_empty_no_eqs) h_mc
            · cases h_mc with
              | error_passthrough _ _ _ _ => rfl
              | unify_success_raw => simp_all
              | unify_no_match_raw => simp_all
              | unify_bad_arity => simp_all
              | switch_minimal_result => simp_all
              | switch_minimal_bad_shape => simp_all
              | no_match _ _ _ _ _ _ _ => rfl
              | grounded_ok => simp_all
              | grounded_runtime_error => simp_all
              | grounded_no_reduce => simp_all
              | grounded_incorrect_arg => simp_all
              | grounded_empty_results => simp_all
              | equation_match => simp_all
              | empty_results => simp_all
            · rw [hA] at h_mc ⊢
              exact mettaCall_untyped_inert
                (by
                  unfold HeadNotExecutable
                  exact ⟨h_head_not_exec, h_head_not_unify, h_head_not_switch⟩)
                (h_head_no_eqs ta) h_mc
          subst h_r
          have h_src_call : MettaCall space d tupleResult.1
              Atom.undefinedType rb1 (tupleResult.1, rb1) := by
            rcases h_shape_A with hA | hA | ⟨ta, hA⟩
            · rw [hA]
              exact MettaCall.no_match _ _ _ fuel rfl
                (by simp [Atom.empty]) (by
                  simpa [Atom.empty] using h_empty_no_eqs fuel)
            · exact MettaCall.error_passthrough _ _ _ hA
            · rw [hA]
              exact MettaCall.no_match _ _ _ fuel
                (isErrorAtom_expr_false ta h_head_nes)
                ⟨h_head_not_exec, h_head_not_unify, h_head_not_switch⟩
                (h_head_no_eqs ta fuel)
          exact ⟨rb1, EvalAtom.interpret_error _ _ _ _ h_src_ok
            (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
              Atom.expressionType, Atom.variableType])
            rfl
            (by intro h_unit; simp [Atom.unit] at h_unit)
            (InterpretExpression.tuple_path _ _ _
              (tupleResult.1, rb1) (tupleResult.1, rb1)
              ⟨Atom.undefinedType, by simp [h_head_untyped], Or.inr rfl⟩
              h_src_tuple h_src_call)
            h_is_error⟩

/-- **The certified fragment** (design note S3): coarse steps whose
soundness against the official declarative semantics is provable with
the S0–S2 machinery — nested congruence over grounded/equation leaf
redexes, with Q-domain spectators and constructor-like congruence heads.
`FragStep ⊆ HESmallStep` is `fragStep_isStep` below. -/
inductive FragStep (space : Space) (d : GroundedDispatch) (fuel : Nat) :
    Atom → Atom → Prop where
  /-- Grounded leaf redex: executable head over Q-domain arguments;
  the dispatched result carries empty bindings (arithmetic-style ops). -/
  | grounded_leaf {op : Atom} {args : List Atom} {rs : ResultSet} {r0 : Atom}
      (h_op_q : SelfEvalQuiescent space d fuel op)
      (h_op_untyped : Atom.undefinedType ∈ getAtomTypes space op)
      (h_args : ∀ a ∈ args, SelfEvalQuiescent space d fuel a)
      (h_args_ne : args ≠ [])
      (h_last : ∀ es', (op :: args).getLast? = some (Atom.expression es') → False)
      (h_nes : ∀ e ∈ op :: args, e ≠ Atom.symbol "Error")
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_exec : d.isExecutable op = true)
      (h_run : d.execute op args = .ok rs)
      (h_mem : (r0, Bindings.empty) ∈ rs) :
      FragStep space d fuel (.expression (op :: args)) r0
  /-- Equation leaf redex: loop-free match whose applied right-hand side
  is itself in Q's domain (constructor-headed rhs). -/
  | equation_leaf {op e2 : Atom} {rest : List Atom} {rhs : Atom} {qb : Bindings}
      (h_elems : ∀ e ∈ op :: e2 :: rest, SelfEvalQuiescent space d fuel e)
      (h_last : ∀ es', (op :: e2 :: rest).getLast? = some (Atom.expression es') → False)
      (h_nes : ∀ e ∈ op :: e2 :: rest, e ≠ Atom.symbol "Error")
      (h_op_has : ∃ t ∈ getAtomTypes space op,
        isFunctionType t = false ∨ t = Atom.undefinedType)
      (h_not_exec : d.isExecutable op = false)
      (h_not_unify : op ≠ .symbol "unify")
      (h_not_switch : op ≠ .symbol "switch-minimal")
      (h_query : (rhs, qb) ∈ queryEquations space
        (.expression (op :: e2 :: rest)) fuel)
      (h_no_loop : qb.hasLoop = false)
      (h_applied_q : SelfEvalQuiescent space d fuel (qb.apply rhs fuel)) :
      FragStep space d fuel (.expression (op :: e2 :: rest)) (qb.apply rhs fuel)
  /-- Congruence at a non-head position with a constructor-like head and
  Q-domain spectators.  (In the fragment the head is never steppable, so
  leftmost coarse congruence is always at position ≥ 1.) -/
  | congruence {p : Atom} {ps : List Atom} {inner inner' : Atom}
      {post : List Atom}
      (h_pre : ∀ e ∈ p :: ps, SelfEvalQuiescent space d fuel e)
      (h_post : ∀ e ∈ post, SelfEvalQuiescent space d fuel e)
      (h_post_last : ∀ es', post.getLast? = some (Atom.expression es') → False)
      (h_post_nes : ∀ e ∈ post, e ≠ Atom.symbol "Error")
      (h_head_nes : p ≠ Atom.symbol "Error")
      (h_head_untyped : getAtomTypes space p = [Atom.undefinedType])
      (h_head_not_exec : d.isExecutable p = false)
      (h_head_not_unify : p ≠ .symbol "unify")
      (h_head_not_switch : p ≠ .symbol "switch-minimal")
      (h_head_no_eqs : ∀ (es : List Atom) (f : Nat),
        queryEquations space (.expression (p :: es)) f = [])
      (h_inner : FragStep space d fuel inner inner') :
      FragStep space d fuel
        (.expression (p :: ps ++ inner :: post))
        (.expression (p :: ps ++ inner' :: post))

/-- **S3: the fragment master absorption theorem.**  Every official
evaluation of a `FragStep` successor (at `%Undefined%`, empty incoming
bindings) is an official evaluation of the source at the result-atom
level.  By induction on the fragment step: leaf redexes assemble the
official derivation directly (`tuple_self` + the matching `MettaCall`
constructor + the premise/Q); congruence is S2 with the induction
hypothesis as the substitution. -/
theorem evalAtom_absorbs_fragStep {space : Space} {d : GroundedDispatch}
    {fuel : Nat}
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = []) :
    ∀ {a a' : Atom}, FragStep space d fuel a a' →
    ∀ {r : ResultPair},
      EvalAtom space d a' Atom.undefinedType Bindings.empty r →
      ∃ rb, EvalAtom space d a Atom.undefinedType Bindings.empty (r.1, rb) := by
  intro a a' h_step
  induction h_step with
  | @grounded_leaf op args rs r0 h_op_q h_op_untyped h_args h_args_ne
      h_last h_nes h_not_unify h_not_switch h_exec h_run h_mem =>
      intro r h_eval
      have h_src_ok : isEmptyOrError (Atom.expression (op :: args)) = false :=
        isEmptyOrError_expr_false _ (h_nes op (by simp))
      have h_elems_all : ∀ e ∈ op :: args, SelfEvalQuiescent space d fuel e := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact h_op_q
        · exact h_args e he'
      have h_tuple : InterpretTuple space d (.expression (op :: args))
          Bindings.empty (.expression (op :: args), Bindings.empty) := by
        cases args with
        | nil => exact absurd rfl h_args_ne
        | cons a1 as =>
            exact tuple_self op a1 as Bindings.empty
              (fun e he b' => selfEval_of_quiescent e (h_elems_all e he) b')
              (fun e he => (h_elems_all e he).not_empty_or_error)
              h_last h_nes
      have h_call : MettaCall space d (.expression (op :: args))
          Atom.undefinedType Bindings.empty r :=
        MettaCall.grounded_ok _ _ _ op args rs (r0, Bindings.empty)
          Bindings.empty r (fuel + 1) rfl h_exec
          h_not_unify
          h_not_switch
          (isErrorAtom_expr_false _ (h_nes op (by simp)))
          h_run h_mem
          (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
          h_eval
      have h_interp : InterpretExpression space d (.expression (op :: args))
          Atom.undefinedType Bindings.empty r :=
        InterpretExpression.tuple_path _ _ _
          (.expression (op :: args), Bindings.empty) r
          ⟨Atom.undefinedType, by simpa using h_op_untyped, Or.inr rfl⟩
          h_tuple h_call
      by_cases hRerr : isErrorAtom r.1 = true
      · exact ⟨r.2, EvalAtom.interpret_error _ _ _ _ h_src_ok
          (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.expressionType, Atom.variableType])
          rfl
          (by intro h_unit; simp [Atom.unit] at h_unit)
          h_interp hRerr⟩
      · exact ⟨r.2, EvalAtom.interpret_success _ _ _ _ h_src_ok
          (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.expressionType, Atom.variableType])
          rfl
          (by intro h_unit; simp [Atom.unit] at h_unit)
          h_interp (by simpa using hRerr)⟩
  | @equation_leaf op e2 rest rhs qb h_elems h_last h_nes h_op_has
      h_not_exec h_not_unify h_not_switch h_query h_no_loop h_applied_q =>
      intro r h_eval
      have h_r := selfEval_unique _ h_applied_q h_eval
      have h_src_ok : isEmptyOrError (Atom.expression (op :: e2 :: rest)) = false :=
        isEmptyOrError_expr_false _ (h_nes op (by simp))
      cases fuel with
      | zero =>
          rw [queryEquations_zero] at h_query
          cases h_query
      | succ n =>
          have h_tuple : InterpretTuple space d
              (.expression (op :: e2 :: rest)) Bindings.empty
              (.expression (op :: e2 :: rest), Bindings.empty) :=
            tuple_self op e2 rest Bindings.empty
              (fun e he b' => selfEval_of_quiescent e (h_elems e he) b')
              (fun e he => (h_elems e he).not_empty_or_error)
              h_last h_nes
          have h_call : MettaCall space d (.expression (op :: e2 :: rest))
              Atom.undefinedType Bindings.empty
              (qb.apply rhs (n + 1), qb) :=
            MettaCall.equation_match _ _ _ rhs qb qb
              (qb.apply rhs (n + 1), qb) (n + 1)
              (isErrorAtom_expr_false _ (h_nes op (by simp)))
              ⟨h_not_exec, h_not_unify, h_not_switch⟩ h_query
              (by rw [mergeBindings_empty_right]; exact List.mem_singleton.mpr rfl)
              h_no_loop
              (selfEval_of_quiescent _ h_applied_q qb)
          rw [h_r]
          refine ⟨qb, EvalAtom.interpret_success _ _ _ _ h_src_ok
            (by simp [getMetaType, Atom.undefinedType, Atom.atomType,
              Atom.expressionType, Atom.variableType])
            rfl
            (by intro h_unit; simp [Atom.unit] at h_unit)
            (InterpretExpression.tuple_path _ _ _
              (.expression (op :: e2 :: rest), Bindings.empty)
              (qb.apply rhs (n + 1), qb)
              (by simpa using h_op_has)
              h_tuple h_call)
            ?_⟩
          have h_ok := h_applied_q.not_empty_or_error
          simp only [isEmptyOrError, Bool.or_eq_false_iff] at h_ok
          exact h_ok.2
  | @congruence p ps inner inner' post h_pre h_post h_post_last h_post_nes
      h_head_nes h_head_untyped h_head_not_exec h_head_not_unify h_head_not_switch
      h_head_no_eqs h_inner ih =>
      intro r h_eval
      exact evalAtom_swap_atom (fun r' h' => ih h') p ps
        h_pre h_post h_post_last h_post_nes h_head_nes h_head_untyped
        h_head_not_exec h_head_not_unify h_head_not_switch
        h_head_no_eqs h_empty_no_eqs h_eval

/-- **S4, chain source-progress half.**  When the chain's source takes a
fragment step, every official evaluation of the *successor* source yields
an official `MinimalStep.chain` execution of the *source* chain whose
substituted result atom is the same.  Together with
`minimalStep_absorbs_chain_subst` (the substitution half), this certifies
the coarse `HES_Chain` decomposition against the official instruction on
the fragment, at the result-atom level. -/
theorem minimalStep_absorbs_chain_source {space : Space}
    {d : GroundedDispatch} {fuel : Nat} {a a' : Atom} {v : String} {t : Atom}
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_frag : FragStep space d fuel a a')
    {er : ResultPair}
    (h_eval' : EvalAtom space d a' Atom.undefinedType Bindings.empty er)
    (h_not_empty : er.1 ≠ Atom.empty) :
    ∃ rb : Bindings,
      MinimalStep d space (.expression [.symbol "chain", a, .var v, t])
      Bindings.empty space
      ((Bindings.assign rb v er.1).applyDefault t,
        Bindings.assign rb v er.1) := by
  obtain ⟨rb, h_eval⟩ := evalAtom_absorbs_fragStep h_empty_no_eqs h_frag h_eval'
  exact ⟨rb, MinimalStep.chain space a v t Bindings.empty (er.1, rb)
    h_eval h_not_empty⟩

/-- **S4, congruence rule.**  The coarse leftmost-congruence rule's
content on the fragment: a congruence-shaped fragment step is absorbed by
official evaluation (this is `evalAtom_absorbs_fragStep` specialized to
the congruence constructor, named as the rule's certification theorem). -/
theorem evalAtom_absorbs_congruence_frag {space : Space}
    {d : GroundedDispatch} {fuel : Nat}
    {p : Atom} {ps : List Atom} {inner inner' : Atom} {post : List Atom}
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_pre : ∀ e ∈ p :: ps, SelfEvalQuiescent space d fuel e)
    (h_post : ∀ e ∈ post, SelfEvalQuiescent space d fuel e)
    (h_post_last : ∀ es', post.getLast? = some (Atom.expression es') → False)
    (h_post_nes : ∀ e ∈ post, e ≠ Atom.symbol "Error")
    (h_head_nes : p ≠ Atom.symbol "Error")
    (h_head_untyped : getAtomTypes space p = [Atom.undefinedType])
    (h_head_not_exec : d.isExecutable p = false)
    (h_head_not_unify : p ≠ .symbol "unify")
    (h_head_not_switch : p ≠ .symbol "switch-minimal")
    (h_head_no_eqs : ∀ (es : List Atom) (f : Nat),
      queryEquations space (.expression (p :: es)) f = [])
    (h_inner : FragStep space d fuel inner inner')
    {r : ResultPair}
    (h_eval : EvalAtom space d (.expression (p :: ps ++ inner' :: post))
      Atom.undefinedType Bindings.empty r) :
    ∃ rb, EvalAtom space d (.expression (p :: ps ++ inner :: post))
      Atom.undefinedType Bindings.empty (r.1, rb) :=
  evalAtom_absorbs_fragStep h_empty_no_eqs
    (FragStep.congruence h_pre h_post h_post_last h_post_nes h_head_nes
      h_head_untyped h_head_not_exec h_head_not_unify h_head_not_switch
      h_head_no_eqs h_inner)
    h_eval

end Mettapedia.Languages.MeTTa.HE
