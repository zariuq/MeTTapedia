import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# Theorem Q: Quiescent Atoms Self-Evaluate Officially

Companion to the master absorption theorem (see
`docs/plans/2026-06-10_correspondence_master_theorem_design.txt` in the
CeTTa repository): on a characterized domain, coarse-quiescent atoms
evaluate to themselves under the official declarative semantics.

The domain (`SelfEvalQuiescent`) is deliberately the honest fragment:

* untyped (`%Undefined%`-typed) heads only, so the tuple path applies and
  no type errors arise (design-note trap T1: function-typed stuck heads can
  officially evaluate to `BadType` errors — *excluded*, not hand-waved);
* no matching equations and non-executable heads (trap T2: no-match sugar
  shapes officially evaluate to Empty — excluded by shape);
* expressions need **at least two elements and a non-expression last
  element** — discovered here (trap T6): the official `InterpretTuple`
  *unwraps* singletons (`(x)` evaluates to `x`'s result, not a 1-tuple),
  and its tail-splice combination changes shape when the final tail
  singleton is expression-valued.  Self-evaluation is simply *false*
  outside this fragment, so the domain says so.

Payoff: `minimalStep_absorbs_chain_subst` — the substitution half of
`HES_Chain`'s correspondence with the official `MinimalStep.chain`
instruction, on the characterized domain.  (The source-progress half needs
the master theorem M; we state only what we prove.)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- `matchTypes` with `%Undefined%` on the left succeeds at any fuel (the
short-circuit branch is fuel-independent). -/
theorem matchTypes_undefined_left_fuel (t : Atom) (b : Bindings) (fuel : Nat) :
    matchTypes Atom.undefinedType t b fuel = [b] := by
  simp [matchTypes]

/-- An atom whose only type is `%Undefined%` type-casts to itself (with the
incoming bindings) under any expected type, at any fuel. -/
theorem typeCast_self_of_undefined {space : Space} {a : Atom}
    (h : getAtomTypes space a = [Atom.undefinedType])
    (t : Atom) (b : Bindings) (fuel : Nat) :
    typeCast a t space b fuel = [(a, b)] := by
  unfold typeCast
  rw [h]
  simp [typeCast.typeCastLoop, matchTypes_undefined_left_fuel]

/-- An expression headed by anything other than the bare `"Error"` symbol
is not Error-shaped. -/
theorem isErrorAtom_expr_false {y : Atom} (zs : List Atom)
    (hy : y ≠ Atom.symbol "Error") :
    isErrorAtom (.expression (y :: zs)) = false := by
  cases y with
  | symbol s =>
      by_cases hs : s = "Error"
      · exact absurd (by rw [hs]) hy
      · simp [isErrorAtom, hs]
  | var v => rfl
  | grounded g => rfl
  | expression es => rfl

/-- Expressions are never the `Empty` symbol. -/
theorem isEmptyAtom_expr_false (l : List Atom) :
    isEmptyAtom (.expression l) = false := by
  simp [isEmptyAtom, Atom.empty]

theorem isEmptyOrError_expr_false {y : Atom} (zs : List Atom)
    (hy : y ≠ Atom.symbol "Error") :
    isEmptyOrError (.expression (y :: zs)) = false := by
  simp [isEmptyOrError, isEmptyAtom_expr_false, isErrorAtom_expr_false zs hy]

/-- **Q's domain**: officially-self-evaluating quiescent atoms. -/
inductive SelfEvalQuiescent (space : Space) (d : GroundedDispatch)
    (fuel : Nat) : Atom → Prop where
  | symbol {s : String}
      (h_not_err : isEmptyOrError (Atom.symbol s) = false)
      (h_untyped : getAtomTypes space (Atom.symbol s) = [Atom.undefinedType]) :
      SelfEvalQuiescent space d fuel (.symbol s)
  | grounded {g : GroundedValue}
      (h_untyped : getAtomTypes space (Atom.grounded g) = [Atom.undefinedType]) :
      SelfEvalQuiescent space d fuel (.grounded g)
  | expr {op e2 : Atom} {rest : List Atom}
      (h_not_err : isEmptyOrError (Atom.expression (op :: e2 :: rest)) = false)
      (h_not_exec : HeadNotExecutable d (.expression (op :: e2 :: rest)))
      (h_no_eqs : ∀ f, queryEquations space (.expression (op :: e2 :: rest)) f = [])
      (h_head_untyped : getAtomTypes space op = [Atom.undefinedType])
      (h_last_flat : ∀ es', (op :: e2 :: rest).getLast? = some (Atom.expression es') → False)
      (h_no_error_sym : ∀ e ∈ op :: e2 :: rest, e ≠ Atom.symbol "Error")
      (h_elems : ∀ e ∈ op :: e2 :: rest, SelfEvalQuiescent space d fuel e) :
      SelfEvalQuiescent space d fuel (.expression (op :: e2 :: rest))

/-- Domain atoms are never Empty/Error. -/
theorem SelfEvalQuiescent.not_empty_or_error {space : Space}
    {d : GroundedDispatch} {fuel : Nat} {a : Atom}
    (h : SelfEvalQuiescent space d fuel a) : isEmptyOrError a = false := by
  cases h with
  | symbol h_not_err _ => exact h_not_err
  | grounded _ => rfl
  | expr h_not_err _ _ _ _ _ _ => exact h_not_err

/-- Tail-tuple self-evaluation: a list of self-evaluating, non-Empty/Error
elements, with at least two entries and a non-expression last element,
tuple-evaluates to itself.  (The base case is the *pair*: the official
singleton constructor unwraps, and the success-combination re-wraps a
non-expression unwrapped tail back into place.) -/
theorem tuple_self {space : Space} {d : GroundedDispatch} :
    ∀ (x y : Atom) (zs : List Atom) (b : Bindings),
      (∀ e ∈ x :: y :: zs, ∀ b' : Bindings,
        EvalAtom space d e Atom.undefinedType b' (e, b')) →
      (∀ e ∈ x :: y :: zs, isEmptyOrError e = false) →
      (∀ es', (x :: y :: zs).getLast? = some (Atom.expression es') → False) →
      (∀ e ∈ x :: y :: zs, e ≠ Atom.symbol "Error") →
      InterpretTuple space d (.expression (x :: y :: zs)) b
        (.expression (x :: y :: zs), b)
  | x, y, [], b, h_eval, h_ok, h_last, h_nes => by
      have h_y : InterpretTuple space d (.expression [y]) b (y, b) :=
        InterpretTuple.singleton y b (y, b)
          (h_eval y (by simp) b)
      have h_comb := InterpretTuple.success x [y] b (x, b) (y, b)
        (by simp)
        (h_eval x (by simp) b)
        (h_ok x (by simp))
        h_y
        (h_ok y (by simp))
      -- the unwrapped tail y is non-expression, so the splice re-wraps it
      cases y with
      | expression es' => exact absurd (by simp) (h_last es')
      | symbol s => simpa using h_comb
      | var v => simpa using h_comb
      | grounded g => simpa using h_comb
  | x, y, z :: zs, b, h_eval, h_ok, h_last, h_nes => by
      have h_tl : InterpretTuple space d (.expression (y :: z :: zs)) b
          (.expression (y :: z :: zs), b) :=
        tuple_self y z zs b
          (fun e he b' => h_eval e (List.mem_cons_of_mem x he) b')
          (fun e he => h_ok e (List.mem_cons_of_mem x he))
          (fun es' h' => h_last es' (by simpa using h'))
          (fun e he => h_nes e (List.mem_cons_of_mem x he))
      have h_comb := InterpretTuple.success x (y :: z :: zs) b
        (x, b) (.expression (y :: z :: zs), b)
        (by simp)
        (h_eval x (by simp) b)
        (h_ok x (by simp))
        h_tl
        (isEmptyOrError_expr_false (z :: zs) (h_nes y (by simp)))
      simpa using h_comb

/-- **Theorem Q** (quiescent self-evaluation): on the characterized domain,
atoms officially evaluate to themselves with unchanged bindings, under
`%Undefined%` expected type. -/
theorem selfEval_of_quiescent {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    (a : Atom) → SelfEvalQuiescent space d fuel a → (b : Bindings) →
      EvalAtom space d a Atom.undefinedType b (a, b)
  | a, h, b => by
    cases h with
    | @symbol s h_not_err h_untyped =>
        refine EvalAtom.type_cast _ _ _ _ fuel h_not_err ?_ (Or.inl rfl) ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.symbolType, Atom.variableType]
        · rw [typeCast_self_of_undefined h_untyped]
          exact List.mem_singleton.mpr rfl
    | @grounded g h_untyped =>
        refine EvalAtom.type_cast _ _ _ _ fuel rfl ?_ (Or.inr (Or.inl rfl)) ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.groundedType, Atom.variableType]
        · rw [typeCast_self_of_undefined h_untyped]
          exact List.mem_singleton.mpr rfl
    | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
        have h_elem_eval : ∀ e ∈ op :: e2 :: rest, ∀ b' : Bindings,
            EvalAtom space d e Atom.undefinedType b' (e, b') := by
          intro e he b'
          exact selfEval_of_quiescent e (h_elems e he) b'
        have h_elem_ok : ∀ e ∈ op :: e2 :: rest, isEmptyOrError e = false :=
          fun e he => (h_elems e he).not_empty_or_error
        have h_tuple : InterpretTuple space d (.expression (op :: e2 :: rest)) b
            (.expression (op :: e2 :: rest), b) :=
          tuple_self op e2 rest b h_elem_eval h_elem_ok h_last h_nes
        have h_not_err_atom : isErrorAtom (Atom.expression (op :: e2 :: rest)) = false := by
          simp only [isEmptyOrError, Bool.or_eq_false_iff] at h_not_err
          exact h_not_err.2
        refine EvalAtom.interpret_success _ _ _ _ h_not_err ?_ rfl ?_ ?_ ?_
        · simp [getMetaType, Atom.undefinedType, Atom.atomType,
            Atom.variableType, Atom.expressionType]
        · intro h_unit
          simp [Atom.unit] at h_unit
        · refine InterpretExpression.tuple_path _ _ _
            (.expression (op :: e2 :: rest), b)
            (.expression (op :: e2 :: rest), b)
            ⟨Atom.undefinedType, by simp [h_head_untyped], Or.inr rfl⟩
            h_tuple ?_
          exact MettaCall.no_match _ _ _ fuel h_not_err_atom
            (by
              revert h_not_exec
              unfold HeadNotExecutable
              exact fun h => h)
            (h_no_eqs fuel)
        · exact h_not_err_atom
  termination_by a _ _ => sizeOf a
  decreasing_by
    have h1 : sizeOf e < sizeOf (op :: e2 :: rest) := List.sizeOf_lt_of_mem he
    have h2 : sizeOf (Atom.expression (op :: e2 :: rest)) =
        1 + sizeOf (op :: e2 :: rest) := by
      simp [Atom.expression.sizeOf_spec]
    omega

/-- Tail-tuple uniqueness: with all elements in Q's domain (and the shape
conditions), self-evaluation is the ONLY tuple evaluation.  Element
uniqueness is a hypothesis (supplied by `selfEval_unique`'s recursion). -/
theorem tuple_unique_of {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    ∀ (x y : Atom) (zs : List Atom) {b : Bindings} {r : ResultPair},
      (∀ e ∈ x :: y :: zs, SelfEvalQuiescent space d fuel e) →
      (∀ e ∈ x :: y :: zs, ∀ {b' : Bindings} {r' : ResultPair},
        EvalAtom space d e Atom.undefinedType b' r' → r' = (e, b')) →
      (∀ es', (x :: y :: zs).getLast? = some (Atom.expression es') → False) →
      (∀ e ∈ x :: y :: zs, e ≠ Atom.symbol "Error") →
      InterpretTuple space d (.expression (x :: y :: zs)) b r →
      r = (.expression (x :: y :: zs), b)
  | x, y, zs, b, r, h_elems, h_uniq, h_last, h_nes, h => by
    cases h with
    | @head_error _ _ _ _ h_ne h_ev h_isErr =>
        have hr := h_uniq x (by simp) h_ev
        have h_ok := (h_elems x (by simp)).not_empty_or_error
        rw [hr] at h_isErr
        simp [h_isErr] at h_ok
    | @tail_error _ _ _ hr _ h_ne h_ev h_hok h_tail h_terr =>
        have hx := h_uniq x (by simp) h_ev
        subst hx
        cases zs with
        | nil =>
            cases h_tail with
            | @singleton _ _ _ h_ev_y =>
                have hy := h_uniq y (by simp) h_ev_y
                have h_ok := (h_elems y (by simp)).not_empty_or_error
                rw [hy] at h_terr
                simp [h_terr] at h_ok
            | @head_error _ _ _ _ h_ne' _ _ => exact absurd rfl h_ne'
            | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
            | @success _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
        | cons z zs' =>
            have h_tl := tuple_unique_of y z zs'
              (fun e he => h_elems e (List.mem_cons_of_mem x he))
              (fun e he => h_uniq e (List.mem_cons_of_mem x he))
              (fun es' h' => h_last es' (by simpa using h'))
              (fun e he => h_nes e (List.mem_cons_of_mem x he))
              h_tail
            rw [h_tl] at h_terr
            have h_ok := isEmptyOrError_expr_false (z :: zs')
              (h_nes y (by simp))
            simp [h_terr] at h_ok
    | @success _ _ _ hr tr h_ne h_ev h_hok h_tl h_tok =>
        have hx := h_uniq x (by simp) h_ev
        subst hx
        cases zs with
        | nil =>
            cases h_tl with
            | @singleton _ _ _ h_ev_y =>
                have hy := h_uniq y (by simp) h_ev_y
                subst hy
                cases y with
                | expression es' => exact absurd (by simp) (h_last es')
                | symbol s => rfl
                | var v => rfl
                | grounded g => rfl
            | @head_error _ _ _ _ h_ne' _ _ => exact absurd rfl h_ne'
            | @tail_error _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
            | @success _ _ _ _ _ h_ne' _ _ _ _ => exact absurd rfl h_ne'
        | cons z zs' =>
            have h_tl' := tuple_unique_of y z zs'
              (fun e he => h_elems e (List.mem_cons_of_mem x he))
              (fun e he => h_uniq e (List.mem_cons_of_mem x he))
              (fun es' h' => h_last es' (by simpa using h'))
              (fun e he => h_nes e (List.mem_cons_of_mem x he))
              h_tl
            subst h_tl'
            rfl

/-- `MettaCall` inertness on the untyped-inert shape: with a non-executable
head, no matching equations at any fuel, and a non-Error shape, the call
returns the atom unchanged — `no_match` and `error_passthrough` are the
only constructors that survive, and both return `(atom, b)`. -/
theorem mettaCall_untyped_inert {space : Space} {d : GroundedDispatch}
    {es : List Atom} {t : Atom} {b : Bindings} {r : ResultPair}
    (h_not_exec : HeadNotExecutable d (.expression es))
    (h_no_eqs : ∀ f, queryEquations space (.expression es) f = [])
    (h : MettaCall space d (.expression es) t b r) :
    r = (.expression es, b) := by
  unfold HeadNotExecutable at h_not_exec
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

/-- **Theorem S0 (Q-uniqueness)**: on Q's domain, self-evaluation is the
ONLY official evaluation — every `EvalAtom` derivation at `%Undefined%`
returns the atom itself with unchanged bindings.  This pins arbitrary
successor derivations in the master-absorption transport (design note S0). -/
theorem selfEval_unique {space : Space} {d : GroundedDispatch}
    {fuel : Nat} :
    (a : Atom) → SelfEvalQuiescent space d fuel a →
    ∀ {b : Bindings} {r : ResultPair},
      EvalAtom space d a Atom.undefinedType b r → r = (a, b)
  | a, h_dom, b, r, h => by
    cases h with
    | empty_or_error _ _ _ _ => rfl
    | type_pass _ _ _ _ _ => rfl
    | @type_cast _ _ _ _ fuel' h_ne h_np h_branch h_result =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            rw [typeCast_self_of_undefined h_untyped] at h_result
            exact List.mem_singleton.mp h_result
        | grounded h_untyped =>
            rw [typeCast_self_of_undefined h_untyped] at h_result
            exact List.mem_singleton.mp h_result
        | expr _ _ _ _ _ _ _ =>
            rcases h_branch with h' | h' | h'
            · simp [getMetaType, Atom.symbolType, Atom.expressionType] at h'
            · simp [getMetaType, Atom.groundedType, Atom.expressionType] at h'
            · simp [Atom.unit] at h'
    | interpret_success _ _ _ _ _ _ h_expr h_not_unit h_interp h_not_error =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            simp [getMetaType, Atom.symbolType, Atom.expressionType] at h_expr
        | grounded h_untyped =>
            simp [getMetaType, Atom.groundedType, Atom.expressionType] at h_expr
        | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
            cases h_interp with
            | function_path =>
                simp_all [isFunctionType, Atom.undefinedType]
            | op_type_error =>
                simp_all [isFunctionType, Atom.undefinedType]
            | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc =>
                have h_tr : tupleResult = (.expression (op :: e2 :: rest), b) :=
                  tuple_unique_of op e2 rest h_elems
                    (fun e he => selfEval_unique e (h_elems e he))
                    h_last h_nes h_tuple
                rw [h_tr] at h_mc
                exact mettaCall_untyped_inert h_not_exec h_no_eqs h_mc
    | interpret_error _ _ _ _ _ _ h_expr h_not_unit h_interp h_is_error =>
        cases h_dom with
        | symbol h_not_err h_untyped =>
            simp [getMetaType, Atom.symbolType, Atom.expressionType] at h_expr
        | grounded h_untyped =>
            simp [getMetaType, Atom.groundedType, Atom.expressionType] at h_expr
        | @expr op e2 rest h_not_err h_not_exec h_no_eqs h_head_untyped h_last h_nes h_elems =>
            cases h_interp with
            | function_path =>
                simp_all [isFunctionType, Atom.undefinedType]
            | op_type_error =>
                simp_all [isFunctionType, Atom.undefinedType]
            | @tuple_path _ _ _ tupleResult _ h_has h_tuple h_mc =>
                have h_tr : tupleResult = (.expression (op :: e2 :: rest), b) :=
                  tuple_unique_of op e2 rest h_elems
                    (fun e he => selfEval_unique e (h_elems e he))
                    h_last h_nes h_tuple
                rw [h_tr] at h_mc
                exact mettaCall_untyped_inert h_not_exec h_no_eqs h_mc
  termination_by a _ => sizeOf a
  decreasing_by
  all_goals
    have h1 : sizeOf e < sizeOf (op :: e2 :: rest) := List.sizeOf_lt_of_mem he
    have h2 : sizeOf (Atom.expression (op :: e2 :: rest)) =
        1 + sizeOf (op :: e2 :: rest) := by
      simp [Atom.expression.sizeOf_spec]
    have h3 : a = Atom.expression (op :: e2 :: rest) := ‹_›
    rw [h3]
    omega

/-- **Absorption, chain substitution half.**  On Q's domain, the coarse
`HES_Chain` substitution step coincides exactly with the official
`MinimalStep.chain` instruction's result: the official instruction
evaluates the source (to itself, by Q) and substitutes it into the
template with `applyDefault` — precisely the coarse successor. -/
theorem minimalStep_absorbs_chain_subst
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {a : Atom} {v : String} {t : Atom}
    (h_seq : SelfEvalQuiescent space d fuel a)
    (h_not_empty : a ≠ Atom.empty) :
    MinimalStep d space (.expression [.symbol "chain", a, .var v, t])
      Bindings.empty space
      ((Bindings.empty.assign v a).applyDefault t,
        Bindings.empty.assign v a) :=
  MinimalStep.chain space a v t Bindings.empty (a, Bindings.empty)
    (selfEval_of_quiescent a h_seq Bindings.empty)
    h_not_empty

end Mettapedia.Languages.MeTTa.HE
