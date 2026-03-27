import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# HE Evaluator Correctness

Soundness and exactness of the 6 mutual evaluation functions in `Eval.lean`
against the declarative spec in `EvalSpec.lean`.

## Why This Matters

A verified evaluator with a spec-implementation biconditional is the
fundamental unit of trustworthy language infrastructure. Soundness says
the runtime doesn't lie; completeness says the spec doesn't miss anything.
Together they give a **portable certificate**: the biconditional can be
translated to MM0, Metamath, or any future MeTTa dialect's proof system,
because it characterizes the evaluator's behavior *exactly* — no more,
no less.

For MeTTa specifically, multiple implementations exist (HE, PeTTa, CeTTa,
MeTTaIL). The declarative spec in `EvalSpec.lean` is shared; each evaluator
proves its own biconditional against it. This is how you get a verified
language *ecosystem*, not just a verified implementation. One spec, many
runtimes, each with a machine-checked correctness certificate.

This is a concrete step toward the QED manifesto's vision: a global library
of formally verified computational semantics, where trust is established
once in the proof and carried everywhere by the certificate.

The public theorem we want is deliberately user-facing and portable:
the pure declarative HE judgment should coincide with *reachable executable
behavior* (`∃ fuel, ...`). That is the artifact worth transporting across
backends and proof systems. The private sync model in this file is not the
final public story; it is the internal exact bridge that makes the public
story provable.

This mirrors the successful mm-lean4 architecture. There, the public boundary
is not the internal operational witness but an acceptance/spec biconditional.
Likewise here, the long-term target is not "Sync is exact" but "public HE
specification iff executable reachability". The private bridge exists to make
that public theorem honest and maintainable.

One important design lesson from this development is that not every useful
proof invariant belongs in the pure public spec. Evaluator-relative notions
such as fuel-indexed filtered soundness live here in `Correctness.lean`
because they mention the evaluator's computed result sets. That is not a
weakness; it is good abstraction hygiene. Pure spec stays pure, executable
invariants stay attached to the executable proof layer, and the public
biconditional composes them at the right boundary.

## Architecture

**Layer 1 — Soundness** (proved):
- Combined `AllSound fuel` (6-way conjunction) by `Nat.rec` on fuel
- Individual theorems: evaluator membership → `EvalSpec` derivation

**Layer 2 — Private exactness** (proved):
- Fuel-synchronous mirror (`*Sync` inductives) that tracks the evaluator
  step-for-step
- `allEvalToSync` / `allSyncToEval` by `Nat.rec`: evaluator ↔ sync at each fuel
- Per-function `*_exact_at` biconditionals

**Layer 3 — Public reachability soundness** (proved):
- `∃ fuel, r ∈ evaluator ... fuel → EvalSpec ... r`
- mm-lean4-style public surface: existential over fuel, targeting pure spec

**Layer 4 — Public completeness** (frontier):
- desired public theorem: `EvalSpec ... r → ∃ fuel, r ∈ evaluator ... fuel`
- likely path: public aligned bridge witness
  `EvalSpec → aligned completeness witness → Sync → evaluator`
- reason for the intermediate witness: the coarse public spec intentionally
  omits some exact execution-side invariants that the private sync model
  records explicitly
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Auxiliary lemmas -/

private lemma mem_singleton_eq {α : Type*} {a b : α} (h : a ∈ [b]) : a = b := by
  simp [List.mem_cons] at h; exact h

private theorem eqMatch_sound
    (space : Space) (dispatch : GroundedDispatch) (atom type_ : Atom) (b : Bindings)
    (r : ResultPair) (n : Nat)
    (h_ef : isErrorAtom atom = false)
    (h_ng : match atom with | .expression (op :: _) => dispatch.isExecutable op = false | _ => True)
    (ih_eval : ∀ s d a t b' r', r' ∈ evalAtom s d a t b' n → EvalAtom s d a t b' r')
    (hr : r ∈ (if queryEquations space atom n = [] then [(atom, b)]
               else (queryEquations space atom n).flatMap fun x =>
                 (mergeBindings x.2 b n).flatMap fun mb =>
                   if mb.hasLoop = true then []
                   else evalAtom space dispatch (mb.apply x.1 n) type_ mb n)) :
    MettaCall space dispatch atom type_ b r := by
  split at hr
  · rename_i h_eqs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact MettaCall.no_match atom type_ b n h_ef h_ng h_eqs
  · rename_i h_eqs_ne
    rw [List.mem_flatMap] at hr
    obtain ⟨⟨rhs, qb⟩, h_eq, hr2⟩ := hr
    rw [List.mem_flatMap] at hr2
    obtain ⟨mb, h_merge, hr3⟩ := hr2
    split at hr3
    · rename_i h_loop; simp at hr3
    · rename_i h_loop_ne
      have h_loop_f : mb.hasLoop = false := by cases h : mb.hasLoop <;> simp_all
      exact MettaCall.equation_match atom type_ b rhs qb mb r n
        h_ef h_ng h_eq h_merge h_loop_f (ih_eval _ _ _ _ _ _ hr3)

/-! ## Combined soundness proposition -/

/-- All 6 evaluator functions are sound at a given fuel level. -/
private def AllSound (fuel : Nat) : Prop :=
  (∀ space dispatch atom type_ b r,
    r ∈ evalAtom space dispatch atom type_ b fuel →
    EvalAtom space dispatch atom type_ b r) ∧
  (∀ space dispatch atom type_ b r,
    r ∈ interpretExpression space dispatch atom type_ b fuel →
    InterpretExpression space dispatch atom type_ b r) ∧
  (∀ space dispatch atom opType b r,
    r ∈ interpretFunction space dispatch atom opType b fuel →
    ∀ retType, InterpretFunction space dispatch atom opType retType b r) ∧
  (∀ space dispatch args types b r,
    r ∈ interpretArgs space dispatch args types b fuel →
    InterpretArgs space dispatch args types b r) ∧
  (∀ space dispatch atom b r,
    r ∈ interpretTuple space dispatch atom b fuel →
    InterpretTuple space dispatch atom b r) ∧
  (∀ space dispatch atom type_ b r,
    r ∈ mettaCall space dispatch atom type_ b fuel →
    MettaCall space dispatch atom type_ b r)

/-- Helper: extract function_path from funcResults membership -/
private theorem funcResults_to_function_path
    (space : Space) (dispatch : GroundedDispatch)
    (op : Atom) (args : List Atom) (type_ : Atom) (b : Bindings) (r : ResultPair) (n : Nat)
    (ih_func : ∀ (space : Space) (dispatch : GroundedDispatch) (atom opType : Atom) (b : Bindings),
      ∀ r ∈ interpretFunction space dispatch atom opType b n,
        ∀ (retType : Atom), InterpretFunction space dispatch atom opType retType b r)
    (ih_call : ∀ (space : Space) (dispatch : GroundedDispatch) (atom type_ : Atom) (b : Bindings),
      ∀ r ∈ mettaCall space dispatch atom type_ b n, MettaCall space dispatch atom type_ b r)
    (funcType : Atom) (h_ft_mem : funcType ∈ getAtomTypes space op)
    (h_is_func : isFunctionType funcType = true)
    (succs : List Bindings)
    (h_check : checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n = .inr succs)
    (b' : Bindings) (h_b'_mem : b' ∈ succs)
    (interpR : Atom) (interpB : Bindings)
    (h_interp_mem : (interpR, interpB) ∈ interpretFunction space dispatch (.expression (op :: args)) funcType b' n)
    (hr4 : r ∈ mettaCall space dispatch interpR
      (if getFunctionRetType funcType = some Atom.expressionType
       then Atom.undefinedType
       else (getFunctionRetType funcType).getD Atom.undefinedType) interpB n) :
    InterpretExpression space dispatch (.expression (op :: args)) type_ b r :=
  InterpretExpression.function_path
    (.expression (op :: args)) type_ b op args funcType
    (if getFunctionRetType funcType = some Atom.expressionType
     then Atom.undefinedType
     else (getFunctionRetType funcType).getD Atom.undefinedType)
    b' (interpR, interpB) r n
    rfl h_ft_mem h_is_func succs h_check h_b'_mem rfl
    (ih_func _ _ _ _ _ _ h_interp_mem _)
    (ih_call _ _ _ _ _ _ hr4)

/-- Helper: decompose funcResults membership into function_path components -/
private theorem mem_funcResults_sound
    (space : Space) (dispatch : GroundedDispatch)
    (op : Atom) (args : List Atom) (type_ : Atom) (b : Bindings) (r : ResultPair) (n : Nat)
    (ih_func : ∀ (space : Space) (dispatch : GroundedDispatch) (atom opType : Atom) (b : Bindings),
      ∀ r ∈ interpretFunction space dispatch atom opType b n,
        ∀ (retType : Atom), InterpretFunction space dispatch atom opType retType b r)
    (ih_call : ∀ (space : Space) (dispatch : GroundedDispatch) (atom type_ : Atom) (b : Bindings),
      ∀ r ∈ mettaCall space dispatch atom type_ b n, MettaCall space dispatch atom type_ b r)
    (hr : r ∈ (getAtomTypes space op).flatMap fun funcType =>
        if isFunctionType funcType then
          match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
          | .inr succs =>
            succs.flatMap fun b' =>
              (interpretFunction space dispatch (.expression (op :: args)) funcType b' n).flatMap
                fun x => mettaCall space dispatch x.1
                  (if getFunctionRetType funcType = some Atom.expressionType
                   then Atom.undefinedType
                   else (getFunctionRetType funcType).getD Atom.undefinedType) x.2 n
          | .inl _ => []
        else []) :
    InterpretExpression space dispatch (.expression (op :: args)) type_ b r := by
  rw [List.mem_flatMap] at hr
  obtain ⟨funcType, h_ft_mem, hr2⟩ := hr
  split at hr2
  · rename_i h_is_func
    split at hr2
    · rename_i succs h_check
      rw [List.mem_flatMap] at hr2
      obtain ⟨b', h_b'_mem, hr3⟩ := hr2
      rw [List.mem_flatMap] at hr3
      obtain ⟨⟨interpR, interpB⟩, h_interp_mem, hr4⟩ := hr3
      exact funcResults_to_function_path space dispatch op args type_ b r n
        ih_func ih_call funcType h_ft_mem h_is_func succs h_check
        b' h_b'_mem interpR interpB h_interp_mem hr4
    · simp at hr2
  · simp at hr2

private theorem allSound : ∀ fuel, AllSound fuel := by
  intro fuel
  induction fuel with
  | zero =>
    -- All 6 functions return [] at fuel 0, so r ∈ [] is False
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s d a t b r h; simp [evalAtom] at h
    · intro s d a t b r h; simp [interpretExpression] at h
    · intro s d a o b r h; simp [interpretFunction] at h
    · intro s d a t b r h; simp [interpretArgs] at h
    · intro s d a b r h; simp [interpretTuple] at h
    · intro s d a t b r h; simp [mettaCall] at h
  | succ n ih =>
    obtain ⟨ih_eval, ih_interp, ih_func, ih_args, ih_tuple, ih_call⟩ := ih
    refine ⟨?evalAtom_step, ?interpExpr_step, ?interpFunc_step,
            ?interpArgs_step, ?interpTuple_step, ?mettaCall_step⟩
    -- interpretTuple
    case interpTuple_step =>
      intro space dispatch atom b r hr
      simp only [interpretTuple] at hr
      match atom with
      | .expression [single] =>
        exact InterpretTuple.singleton single b r (ih_eval _ _ _ _ _ _ hr)
      | .expression (hd :: hd2 :: rest) =>
        simp only [List.mem_flatMap] at hr
        obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
        split at hr2
        · -- Head error
          rename_i h_err
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2; subst hr2
          exact InterpretTuple.head_error hd (hd2 :: rest) b
            (headR, headB) (by simp)
            (ih_eval _ _ _ _ _ _ h_head_mem) h_err
        · -- Head ok
          rename_i h_err_ne
          have h_err_false : isEmptyOrError headR = false := by
            cases h : isEmptyOrError headR <;> simp_all
          simp only [List.mem_map] at hr2
          obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
          split at hr3
          · -- Tail error
            rename_i h_terr
            obtain ⟨rfl, rfl⟩ := hr3
            exact InterpretTuple.tail_error hd (hd2 :: rest) b
              (headR, headB) (tailR, tailB) (by simp)
              (ih_eval _ _ _ _ _ _ h_head_mem) h_err_false
              (ih_tuple _ _ _ _ _ h_tail_mem) h_terr
          · -- Both ok
            rename_i h_terr_ne
            have h_terr_false : isEmptyOrError tailR = false := by
              cases h : isEmptyOrError tailR <;> simp_all
            obtain ⟨rfl, rfl⟩ := hr3
            exact InterpretTuple.success hd (hd2 :: rest) b
              (headR, headB) (tailR, tailB) (by simp)
              (ih_eval _ _ _ _ _ _ h_head_mem) h_err_false
              (ih_tuple _ _ _ _ _ h_tail_mem) h_terr_false
      | .expression [] => simp at hr
      | .symbol _ => simp at hr
      | .var _ => simp at hr
      | .grounded _ => simp at hr
    -- interpretArgs
    case interpArgs_step =>
      intro space dispatch args types b r hr
      match args, types with
      | [], [] =>
        simp only [interpretArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact InterpretArgs.nil
      | arg :: remArgs, t :: remTypes =>
        simp only [interpretArgs, List.mem_flatMap] at hr
        obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
        by_cases h_cond : (headR != arg && isEmptyOrError headR) = true
        · -- headR ≠ arg ∧ isEmptyOrError headR → head_changed_error
          simp [h_cond] at hr2; subst hr2
          have h_ne : headR ≠ arg := by
            cases h1 : (headR != arg) <;> simp_all [bne_iff_ne]
          have h_err : isEmptyOrError headR = true := by
            cases h1 : isEmptyOrError headR <;> cases h2 : (headR != arg) <;> simp_all
          exact InterpretArgs.head_changed_error arg remArgs t remTypes b
            (headR, headB) (ih_eval _ _ _ _ _ _ h_head_mem) h_err h_ne
        · -- ¬condition → cons path
          have h_cond_false : (headR != arg && isEmptyOrError headR) = false := by
            cases h : headR != arg && isEmptyOrError headR <;> simp_all
          simp [h_cond_false] at hr2
          have h_head_ok : isEmptyOrError headR = false ∨ headR = arg := by
            cases he : isEmptyOrError headR with
            | false => left; rfl
            | true =>
              right; by_contra h_ne
              have : (headR != arg) = true := by simp [bne_iff_ne, h_ne]
              simp [this, he] at h_cond
          obtain ⟨tailR, tailB, h_tail_mem, hr3⟩ := hr2
          split at hr3
          · rename_i h_terr
            obtain ⟨rfl, rfl⟩ := hr3
            exact InterpretArgs.cons_tail_error arg remArgs t remTypes b
              (headR, headB) (tailR, tailB)
              (ih_eval _ _ _ _ _ _ h_head_mem) h_head_ok
              (ih_args _ _ _ _ _ _ h_tail_mem) h_terr
          · rename_i h_terr_ne
            have h_terr_false : isEmptyOrError tailR = false := by
              cases h : isEmptyOrError tailR <;> simp_all
            subst hr3
            exact InterpretArgs.cons_ok arg remArgs t remTypes b
              (headR, headB) (tailR, tailB)
              (ih_eval _ _ _ _ _ _ h_head_mem) h_head_ok
              (ih_args _ _ _ _ _ _ h_tail_mem) h_terr_false
      | [], _ :: _ => simp [interpretArgs] at hr
      | _ :: _, [] => simp [interpretArgs] at hr
    -- interpretFunction
    case interpFunc_step =>
      intro space dispatch atom opType b r hr retType
      match atom with
      | .expression (op :: args) =>
        simp only [interpretFunction, List.mem_flatMap] at hr
        obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
        split at hr2
        · -- Head error
          rename_i h_err
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2; subst hr2
          exact InterpretFunction.head_error _ opType retType b op args
            (headR, headB) rfl (ih_eval _ _ _ _ _ _ h_head_mem) h_err
        · -- Head ok
          rename_i h_err_ne
          have h_err_false : isEmptyOrError headR = false := by
            cases h : isEmptyOrError headR <;> simp_all
          match h_argt : getFunctionArgTypes opType with
          | some argTypes =>
            simp only [h_argt] at hr2
            rw [List.mem_map] at hr2
            obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
            split at hr3
            · rename_i h_terr
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretFunction.head_ok_tail_error _ opType retType b
                op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                (ih_eval _ _ _ _ _ _ h_head_mem) h_err_false
                (ih_args _ _ _ _ _ _ h_tail_mem) h_terr
            · rename_i h_terr_ne
              have h_terr_false : isEmptyOrError tailR = false := by
                cases h : isEmptyOrError tailR <;> simp_all
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretFunction.head_ok_tail_ok _ opType retType b
                op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                (ih_eval _ _ _ _ _ _ h_head_mem) h_err_false
                (ih_args _ _ _ _ _ _ h_tail_mem) h_terr_false
          | none => simp only [h_argt, List.not_mem_nil] at hr2
      | .symbol _ => simp [interpretFunction] at hr
      | .var _ => simp [interpretFunction] at hr
      | .grounded _ => simp [interpretFunction] at hr
      | .expression [] => simp [interpretFunction] at hr
    case mettaCall_step =>
      intro space dispatch atom type_ b r hr
      cases h_err : isErrorAtom atom with
      | true =>
        simp [mettaCall, h_err] at hr
        subst r
        exact MettaCall.error_passthrough atom type_ b h_err
      | false =>
        have h_ef : isErrorAtom atom = false := h_err
        match atom with
        | .expression (op :: args) =>
          cases h_exec : dispatch.isExecutable op with
          | true =>
            simp [mettaCall, h_ef, h_exec] at hr
            cases h_run : dispatch.execute op args with
            | ok results =>
              by_cases h_results : results = []
              · simp [h_run, h_results] at hr
                have hr_eq : r = (Atom.empty, b) := by simpa [h_results] using hr
                subst r
                subst results
                exact MettaCall.grounded_empty_results _ type_ b op args rfl h_exec h_ef h_run
              · simp [h_run, h_results] at hr
                obtain ⟨nativeR, nativeB, h_nat, mb, h_merge, hr3⟩ := hr
                exact MettaCall.grounded_ok _ type_ b op args results
                  (nativeR, nativeB) mb r n rfl h_exec h_ef h_run
                  h_nat h_merge (ih_eval _ _ _ _ _ _ hr3)
            | runtimeError msg =>
              simp [h_run] at hr
              subst r
              exact MettaCall.grounded_runtime_error _ type_ b op args msg rfl h_exec h_ef h_run
            | noReduce =>
              simp [h_run] at hr
              subst r
              exact MettaCall.grounded_no_reduce _ type_ b op args rfl h_exec h_ef h_run
            | incorrectArgument =>
              simp [h_run] at hr
              subst r
              exact MettaCall.grounded_incorrect_arg _ type_ b op args rfl h_exec h_ef h_run
          | false =>
            simp [mettaCall, h_ef, h_exec] at hr
            exact eqMatch_sound space dispatch _ type_ b r n h_ef (by simpa using h_exec)
              ih_eval hr
        | .symbol _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_sound space dispatch _ type_ b r n h_ef trivial ih_eval hr
        | .var _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_sound space dispatch _ type_ b r n h_ef trivial ih_eval hr
        | .grounded _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_sound space dispatch _ type_ b r n h_ef trivial ih_eval hr
        | .expression [] =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_sound space dispatch _ type_ b r n h_ef trivial ih_eval hr
    case evalAtom_step =>
      intro space dispatch atom type_ b r hr
      cases h_empty : isEmptyOrError atom with
      | true =>
        simp [evalAtom, h_empty] at hr
        subst r
        exact EvalAtom.empty_or_error atom type_ b h_empty
      | false =>
        cases h_tyAtom : type_ == Atom.atomType with
        | true =>
          simp [evalAtom, h_empty, h_tyAtom] at hr
          subst r
          exact EvalAtom.type_pass atom type_ b h_empty
            (Or.inl (beq_iff_eq.mp h_tyAtom))
        | false =>
          cases h_tyMeta : type_ == getMetaType atom with
          | true =>
            simp [evalAtom, h_empty, h_tyAtom, h_tyMeta] at hr
            subst r
            exact EvalAtom.type_pass atom type_ b h_empty
              (Or.inr <| Or.inl (beq_iff_eq.mp h_tyMeta))
          | false =>
            cases h_var : getMetaType atom == Atom.variableType with
            | true =>
              simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var] at hr
              subst r
              exact EvalAtom.type_pass atom type_ b h_empty
                (Or.inr <| Or.inr (beq_iff_eq.mp h_var))
            | false =>
              have h_not_pass : ¬(type_ = Atom.atomType
                  ∨ type_ = getMetaType atom
                  ∨ getMetaType atom = Atom.variableType) := by
                intro h_pass
                rcases h_pass with h_pass | h_pass | h_pass
                · simp [h_pass] at h_tyAtom
                · simp [h_pass] at h_tyMeta
                · simp [h_pass] at h_var
              cases h_sym : getMetaType atom == Atom.symbolType with
              | true =>
                simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym] at hr
                exact EvalAtom.type_cast atom type_ b r n h_empty h_not_pass
                  (Or.inl (beq_iff_eq.mp h_sym)) hr
              | false =>
                cases h_grd : getMetaType atom == Atom.groundedType with
                | true =>
                  simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd] at hr
                  exact EvalAtom.type_cast atom type_ b r n h_empty h_not_pass
                    (Or.inr <| Or.inl (beq_iff_eq.mp h_grd)) hr
                | false =>
                  cases h_unit : atom == Atom.unit with
                  | true =>
                    simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd, h_unit] at hr
                    exact EvalAtom.type_cast atom type_ b r n h_empty h_not_pass
                      (Or.inr <| Or.inr (beq_iff_eq.mp h_unit)) hr
                  | false =>
                    cases h_expr : getMetaType atom == Atom.expressionType with
                    | true =>
                      have h_expr_eq : getMetaType atom = Atom.expressionType :=
                        beq_iff_eq.mp h_expr
                      have h_not_unit : atom ≠ Atom.unit := by
                        intro h_eq
                        simp [h_eq] at h_unit
                      simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd, h_unit, h_expr] at hr
                      by_cases h_succ :
                          (!(List.filter (fun x => !isErrorAtom x.1)
                            (interpretExpression space dispatch atom type_ b n)).isEmpty) = true
                      · simp [h_succ, List.mem_filter] at hr
                        obtain ⟨h_interp_mem, h_not_err_bool⟩ := hr
                        have h_not_error : isErrorAtom r.1 = false := by
                          cases h : isErrorAtom r.1 <;> simp_all
                        exact EvalAtom.interpret_success atom type_ b r
                          h_empty h_not_pass h_expr_eq h_not_unit
                          (ih_interp _ _ _ _ _ _ h_interp_mem) h_not_error
                      · have h_succ_false :
                            (!(List.filter (fun x => !isErrorAtom x.1)
                              (interpretExpression space dispatch atom type_ b n)).isEmpty) = false := by
                          cases h : (!(List.filter (fun x => !isErrorAtom x.1)
                            (interpretExpression space dispatch atom type_ b n)).isEmpty) <;> simp_all
                        simp [h_succ_false, List.mem_filter] at hr
                        obtain ⟨h_interp_mem, h_is_error⟩ := hr
                        exact EvalAtom.interpret_error atom type_ b r
                          h_empty h_not_pass h_expr_eq h_not_unit
                          (ih_interp _ _ _ _ _ _ h_interp_mem) h_is_error
                    | false =>
                      cases atom <;> simp [getMetaType] at h_sym h_grd h_var h_expr
    case interpExpr_step =>
      intro space dispatch atom type_ b r hr
      simp only [interpretExpression] at hr
      match atom with
      | .expression (op :: args) =>
        -- Reduce the match in hr: after simp only [interpretExpression], hr has
        -- `match .expression (op :: args) with | .expression (op_1 :: tail) => ...`
        -- Use simp only [] to reduce the match, then normalize (==) to (=)
        simp only [] at hr
        simp only [beq_iff_eq] at hr
        -- Now case split on hasNonFunc Bool
        cases h_hasNonFunc : ((getAtomTypes space op).any
            fun t => !isFunctionType t || t == Atom.undefinedType) with
        | true =>
          simp only [h_hasNonFunc, ite_true] at hr
          -- Split on !allResults.isEmpty
          split at hr
          · -- allResults non-empty
            rename_i h_nonempty
            rw [List.mem_append] at hr
            rcases hr with hr_func | hr_tuple
            · exact mem_funcResults_sound space dispatch op args type_ b r n
                ih_func ih_call hr_func
            · rw [List.mem_flatMap] at hr_tuple
              obtain ⟨⟨tupleR, tupleB⟩, h_tuple_mem, hr3⟩ := hr_tuple
              have h_exists : ∃ t ∈ getAtomTypes space op,
                  isFunctionType t = false ∨ t = Atom.undefinedType := by
                rw [List.any_eq_true] at h_hasNonFunc
                obtain ⟨t, h_t_mem, h_t_prop⟩ := h_hasNonFunc
                simp [Bool.or_eq_true] at h_t_prop
                exact ⟨t, h_t_mem, h_t_prop⟩
              exact InterpretExpression.tuple_path
                (.expression (op :: args)) type_ b
                (tupleR, tupleB) r h_exists
                (ih_tuple _ _ _ _ _ h_tuple_mem)
                (ih_call _ _ _ _ _ _ hr3)
          · -- allResults empty, hasNonFunc = true → !hasNonFunc is false → []
            rename_i h_empty
            simp at hr
        | false =>
          -- hasNonFunc = false: simplify hr
          simp [h_hasNonFunc] at hr
          -- After simp with h_hasNonFunc = false:
          -- tupleResults = [], so allResults = funcResults
          -- Split on !funcResults.isEmpty
          split at hr
          · -- funcResults non-empty
            rename_i h_nonempty
            exact mem_funcResults_sound space dispatch op args type_ b r n
              ih_func ih_call hr
          · -- funcResults empty → error fallback
            rename_i h_empty
            split at hr
            · -- allChecksFailed = true
              rename_i h_all_failed
              rw [List.mem_flatMap] at hr
              obtain ⟨funcType, h_ft_mem, hr2⟩ := hr
              split at hr2
              · rename_i h_is_func
                split at hr2
                · rename_i errs h_check
                  rw [List.mem_map] at hr2
                  obtain ⟨e, h_e_mem, h_eq⟩ := hr2
                  subst h_eq
                  have h_no_nf : ∀ t ∈ getAtomTypes space op,
                      isFunctionType t = true ∧ t ≠ Atom.undefinedType := by
                    intro t h_t_mem
                    have h_f := h_hasNonFunc
                    rw [List.any_eq_false] at h_f
                    have := h_f t h_t_mem
                    constructor
                    · cases h : isFunctionType t
                      · exfalso; simp [h] at this
                      · rfl
                    · intro h_eq; simp [h_eq] at this
                  exact InterpretExpression.op_type_error
                    (.expression (op :: args)) type_ b op args
                    e n funcType errs rfl
                    (fun ft h_ft_mem' h_ft_func => by
                      have := h_all_failed ft h_ft_mem'
                      match h_chk : checkIfFunctionTypeIsApplicable
                          (.expression (op :: args)) ft type_ space b n with
                      | .inl errs' => exact ⟨errs', rfl⟩
                      | .inr _ => simp [h_chk, h_ft_func] at this)
                    (fun t h_t_mem => h_no_nf t h_t_mem)
                    h_ft_mem h_is_func h_check h_e_mem
                · simp at hr2
              · simp at hr2
            · -- allChecksFailed = false → []
              simp at hr
      | .expression [] => simp at hr
      | .symbol _ => simp at hr
      | .var _ => simp at hr
      | .grounded _ => simp at hr

/-! ## Individual soundness theorems -/

/-- Every result of `evalAtom` is derivable in `EvalAtom`. -/
theorem evalAtom_sound (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ evalAtom space dispatch atom type_ b fuel) :
    EvalAtom space dispatch atom type_ b r :=
  (allSound fuel).1 space dispatch atom type_ b r hr

/-- Every result of `interpretExpression` is derivable in `InterpretExpression`. -/
theorem interpretExpression_sound (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ interpretExpression space dispatch atom type_ b fuel) :
    InterpretExpression space dispatch atom type_ b r :=
  (allSound fuel).2.1 space dispatch atom type_ b r hr

/-- Every result of `interpretFunction` is derivable in `InterpretFunction`. -/
theorem interpretFunction_sound (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ interpretFunction space dispatch atom opType b fuel) :
    ∀ retType, InterpretFunction space dispatch atom opType retType b r :=
  (allSound fuel).2.2.1 space dispatch atom opType b r hr

/-- Every result of `interpretArgs` is derivable in `InterpretArgs`. -/
theorem interpretArgs_sound (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ interpretArgs space dispatch args types b fuel) :
    InterpretArgs space dispatch args types b r :=
  (allSound fuel).2.2.2.1 space dispatch args types b r hr

/-- Every result of `interpretTuple` is derivable in `InterpretTuple`. -/
theorem interpretTuple_sound (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ interpretTuple space dispatch atom b fuel) :
    InterpretTuple space dispatch atom b r :=
  (allSound fuel).2.2.2.2.1 space dispatch atom b r hr

/-- Every result of `mettaCall` is derivable in `MettaCall`. -/
theorem mettaCall_sound (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair)
    (hr : r ∈ mettaCall space dispatch atom type_ b fuel) :
    MettaCall space dispatch atom type_ b r :=
  (allSound fuel).2.2.2.2.2 space dispatch atom type_ b r hr

/-! ## Fuel-Indexed Filtered Soundness -/

/-- Fuel-indexed filtered soundness: the evaluator's success-priority filtering
    is correct relative to the results it actually computed at the given subfuel.
    Provable from soundness alone (no completeness needed).
    `n` is the subfuel passed to `interpretExpression` — i.e., one less than
    the parent `evalAtom` fuel `n + 1`.

    This notion intentionally lives in `Correctness.lean`, not `EvalSpec.lean`,
    because it is evaluator-relative: the negative condition quantifies over the
    computed `interpretExpression` result list at subfuel `n`, not just over the
    fuel-free declarative relation.

    The negative condition (all `interpretExpression` results are errors) is guarded
    by `isEmptyOrError atom = false`: when `isEmptyOrError` is true, `evalAtom`
    returns `[(atom, b)]` without consulting `interpretExpression`, so the
    evaluator's filter is not involved and we make no claim about
    `interpretExpression`'s results. -/
def EvalAtomFilteredAtFuel (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (n : Nat) (r : ResultPair) : Prop :=
  EvalAtom space dispatch atom type_ b r ∧
  (isErrorAtom r.1 = true →
    isEmptyOrError atom = false →
    ∀ r' ∈ interpretExpression space dispatch atom type_ b n,
      isErrorAtom r'.1 = true)

/-- For non-expression atoms, `interpretExpression` returns `[]` at any fuel. -/
private theorem interpretExpression_nil_of_not_expr (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat)
    (h : ∀ op args, atom ≠ .expression (op :: args)) :
    interpretExpression space dispatch atom type_ b fuel = [] := by
  cases fuel with
  | zero => simp [interpretExpression]
  | succ n => simp only [interpretExpression]

/-- Every result of `evalAtom` at fuel `n + 1` satisfies the fuel-indexed
    filtered soundness property. The negative condition (errors only when no
    successes exist) is bounded by the subfuel `n` actually used by the evaluator. -/
theorem evalAtom_filtered_sound (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (n : Nat) (r : ResultPair)
    (hr : r ∈ evalAtom space dispatch atom type_ b (n + 1)) :
    EvalAtomFilteredAtFuel space dispatch atom type_ b n r := by
  refine ⟨evalAtom_sound space dispatch atom type_ b (n + 1) r hr, ?_⟩
  intro h_is_err h_not_ee r' h_r'_mem
  -- Case 1: atom is not a proper expression → interpretExpression returns []
  by_cases h_proper : ∃ op args, atom = .expression (op :: args)
  · -- Case 2: atom IS a proper expression
    obtain ⟨op, args, rfl⟩ := h_proper
    -- Navigate evalAtom's if-chain for .expression (op :: args)
    simp only [evalAtom] at hr
    split at hr  -- isEmptyOrError
    · -- isEmptyOrError = true contradicts h_not_ee
      rename_i h_ee; simp [h_not_ee] at h_ee
    · split at hr  -- type pass: type_ == atomType ∨ type_ == getMetaType ∨ variableType
      · -- In this branch r = (atom, b), so isErrorAtom r.1 = isErrorAtom atom.
        -- Since isEmptyOrError atom = false, isErrorAtom atom = false.
        rename_i h_tp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        -- isEmptyOrError false means isErrorAtom atom = false
        simp [isEmptyOrError] at h_not_ee
        obtain ⟨_, h_ne⟩ := h_not_ee
        simp [h_ne] at h_is_err
      · split at hr  -- symbol/grounded/unit → typeCast
        · -- Unreachable for .expression (op :: args):
          -- getMetaType (.expression (op :: args)) = expressionType ≠ symbolType/groundedType
          -- and .expression (op :: args) ≠ unit (unit = .expression [])
          rename_i h_cast
          simp [getMetaType, Atom.symbolType, Atom.groundedType, Atom.expressionType,
                Atom.unit] at h_cast
        · split at hr  -- expression branch (getMetaType == expressionType)
          · -- THE expression branch: r ∈ filter of interpretExpression results
            split at hr  -- successes non-empty?
            · -- Successes non-empty: r is a success → contradicts h_is_err
              rw [List.mem_filter] at hr
              obtain ⟨_, h_not_err⟩ := hr
              simp at h_not_err
              simp [h_not_err] at h_is_err
            · -- Successes empty: ALL interpretExpression results are errors
              rename_i h_succ_empty
              -- h_succ_empty : ¬(!successes.isEmpty) = true, i.e. successes.isEmpty = true
              rw [List.mem_filter] at hr
              obtain ⟨h_r_mem, _⟩ := hr
              -- r' ∈ interpretExpression ... n. Show isErrorAtom r'.1 = true.
              -- The success filter is empty, so no element has !isErrorAtom = true.
              by_contra h_not_err_r'
              push_neg at h_succ_empty
              -- h_succ_empty says the success filter is empty
              -- Convert: ¬(!(filter ...).isEmpty) = true means (filter ...).isEmpty = true
              have h_filt_empty : (List.filter (fun x => !isErrorAtom x.1)
                  (interpretExpression space dispatch
                    (.expression (op :: args)) type_ b n)).isEmpty = true := by
                cases h : (List.filter (fun x => !isErrorAtom x.1)
                  (interpretExpression space dispatch
                    (.expression (op :: args)) type_ b n)).isEmpty <;> simp_all
              rw [List.isEmpty_iff] at h_filt_empty
              have h_ne : isErrorAtom r'.1 = false := by
                cases h : isErrorAtom r'.1 <;> simp_all
              have h_mem_filt : r' ∈ (interpretExpression space dispatch
                  (.expression (op :: args)) type_ b n).filter
                  (fun x => !isErrorAtom x.1) := by
                rw [List.mem_filter]
                exact ⟨h_r'_mem, by simp [h_ne]⟩
              rw [h_filt_empty] at h_mem_filt
              simp at h_mem_filt
          · -- Unreachable: getMetaType (.expression (op :: args)) = expressionType
            rename_i h_not_expr
            simp [getMetaType, Atom.expressionType] at h_not_expr
  · -- Case 1: not a proper expression → interpretExpression returns []
    push_neg at h_proper
    rw [interpretExpression_nil_of_not_expr _ _ _ _ _ _ h_proper] at h_r'_mem
    simp at h_r'_mem

/-! ## Private Synchronous Model

Proof-only bounded relations that mirror the evaluator's exact fuel discipline.
These are intentionally private and are not a second public semantics:
- sibling recursive calls share the same decremented subfuel,
- signatures match the evaluator, not the canonical declarative spec,
- `EvalAtomSync.interpret_error` carries the local no-success condition needed
  for the evaluator's success-priority filter. -/

/-- Private abbreviation for the evaluator-local "all computed results are errors"
condition used by the synchronous mirror of `evalAtom`'s error branch. -/
private def OnlyErrorsAt (results : ResultSet) : Prop :=
  ∀ r ∈ results, isErrorAtom r.1 = true

mutual

/-- Private synchronous model for `evalAtom`. There are no constructors at fuel `0`. -/
private inductive EvalAtomSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → Atom → Atom → Bindings → ResultPair → Prop where
  | empty_or_error (n : Nat) (atom type_ : Atom) (b : Bindings)
      (h : isEmptyOrError atom = true) :
      EvalAtomSync space dispatch (n + 1) atom type_ b (atom, b)
  | type_pass (n : Nat) (atom type_ : Atom) (b : Bindings)
      (h_not_empty : isEmptyOrError atom = false)
      (h_pass : type_ = Atom.atomType
              ∨ type_ = getMetaType atom
              ∨ getMetaType atom = Atom.variableType) :
      EvalAtomSync space dispatch (n + 1) atom type_ b (atom, b)
  | type_cast (n : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_cast_branch : getMetaType atom = Atom.symbolType
                     ∨ getMetaType atom = Atom.groundedType
                     ∨ atom = Atom.unit)
      (h_result : r ∈ typeCast atom type_ space b n) :
      EvalAtomSync space dispatch (n + 1) atom type_ b r
  | interpret_success (n : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpressionSync space dispatch n atom type_ b r)
      (h_not_error : isErrorAtom r.1 = false) :
      EvalAtomSync space dispatch (n + 1) atom type_ b r
  | interpret_error (n : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpressionSync space dispatch n atom type_ b r)
      (h_is_error : isErrorAtom r.1 = true)
      (h_all_errors : OnlyErrorsAt (interpretExpression space dispatch atom type_ b n)) :
      EvalAtomSync space dispatch (n + 1) atom type_ b r

/-- Private synchronous model for `interpretExpression`. -/
private inductive InterpretExpressionSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → Atom → Atom → Bindings → ResultPair → Prop where
  | function_path (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (funcType : Atom) (b' : Bindings)
      (interpResult callResult : ResultPair) (succs : List Bindings)
      (h_shape : atom = .expression (op :: args))
      (h_op_type : funcType ∈ getAtomTypes space op)
      (h_is_func : isFunctionType funcType = true)
      (h_check : checkIfFunctionTypeIsApplicable atom funcType type_ space b n = .inr succs)
      (h_check_b : b' ∈ succs)
      (h_interp : InterpretFunctionSync space dispatch n atom funcType b' interpResult)
      (h_call : MettaCallSync space dispatch n interpResult.1
        (if getFunctionRetType funcType == some Atom.expressionType
         then Atom.undefinedType
         else (getFunctionRetType funcType).getD Atom.undefinedType)
        interpResult.2 callResult) :
      InterpretExpressionSync space dispatch (n + 1) atom type_ b callResult
  | tuple_path (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (tupleResult callResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_has_non_func : ((getAtomTypes space op).any fun t =>
          !isFunctionType t || t == Atom.undefinedType) = true)
      (h_tuple : InterpretTupleSync space dispatch n atom b tupleResult)
      (h_call : MettaCallSync space dispatch n tupleResult.1 type_ tupleResult.2 callResult) :
      InterpretExpressionSync space dispatch (n + 1) atom type_ b callResult
  | op_type_error (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (failedType : Atom) (errs : List Atom) (errAtom : Atom)
      (h_shape : atom = .expression (op :: args))
      (h_has_non_func : ((getAtomTypes space op).any fun t =>
          !isFunctionType t || t == Atom.undefinedType) = false)
      (h_all_fail : ((getAtomTypes space op).all fun funcType =>
          if isFunctionType funcType then
            match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
            | .inl _ => true
            | .inr _ => false
          else true) = true)
      (h_failed_type : failedType ∈ getAtomTypes space op)
      (h_failed_func : isFunctionType failedType = true)
      (h_check_fail : checkIfFunctionTypeIsApplicable atom failedType type_ space b n = .inl errs)
      (h_err_mem : errAtom ∈ errs) :
      InterpretExpressionSync space dispatch (n + 1) atom type_ b (errAtom, b)

/-- Private synchronous model for `interpretFunction`. -/
private inductive InterpretFunctionSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → Atom → Atom → Bindings → ResultPair → Prop where
  | head_error (n : Nat) (atom opType : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (headResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_head : EvalAtomSync space dispatch n op opType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretFunctionSync space dispatch (n + 1) atom opType b headResult
  | head_ok_tail_error (n : Nat) (atom opType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtomSync space dispatch n op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgsSync space dispatch n args argTypes headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretFunctionSync space dispatch (n + 1) atom opType b tailResult
  | head_ok_tail_ok (n : Nat) (atom opType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtomSync space dispatch n op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgsSync space dispatch n args argTypes headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretFunctionSync space dispatch (n + 1) atom opType b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

/-- Private synchronous model for `interpretArgs`. -/
private inductive InterpretArgsSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → List Atom → List Atom → Bindings → ResultPair → Prop where
  | nil (n : Nat) (b : Bindings) :
      InterpretArgsSync space dispatch (n + 1) [] [] b (Atom.unit, b)
  | head_changed_error (n : Nat) (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult : ResultPair)
      (h_head : EvalAtomSync space dispatch n a t b headResult)
      (h_err : isEmptyOrError headResult.1 = true)
      (h_changed : headResult.1 ≠ a) :
      InterpretArgsSync space dispatch (n + 1) (a :: as) (t :: ts) b headResult
  | cons_tail_error (n : Nat) (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtomSync space dispatch n a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgsSync space dispatch n as ts headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretArgsSync space dispatch (n + 1) (a :: as) (t :: ts) b tailResult
  | cons_ok (n : Nat) (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtomSync space dispatch n a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgsSync space dispatch n as ts headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretArgsSync space dispatch (n + 1) (a :: as) (t :: ts) b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

/-- Private synchronous model for `interpretTuple`. -/
private inductive InterpretTupleSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → Atom → Bindings → ResultPair → Prop where
  | singleton (n : Nat) (a : Atom) (b : Bindings) (r : ResultPair)
      (h_eval : EvalAtomSync space dispatch n a Atom.undefinedType b r) :
      InterpretTupleSync space dispatch (n + 1) (.expression [a]) b r
  | head_error (n : Nat) (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomSync space dispatch n hd Atom.undefinedType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretTupleSync space dispatch (n + 1) (.expression (hd :: tl)) b headResult
  | tail_error (n : Nat) (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomSync space dispatch n hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTupleSync space dispatch n (.expression tl) headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretTupleSync space dispatch (n + 1) (.expression (hd :: tl)) b tailResult
  | success (n : Nat) (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomSync space dispatch n hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTupleSync space dispatch n (.expression tl) headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretTupleSync space dispatch (n + 1) (.expression (hd :: tl)) b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

/-- Private synchronous model for `mettaCall`.
    Intentionally omits the canonical-spec `MettaCall.empty_results` constructor:
    this sync layer mirrors the executable evaluator exactly, not the coarser
    canonical declarative semantics. -/
private inductive MettaCallSync (space : Space) (dispatch : GroundedDispatch) :
    Nat → Atom → Atom → Bindings → ResultPair → Prop where
  | error_passthrough (n : Nat) (atom type_ : Atom) (b : Bindings)
      (h_err : isErrorAtom atom = true) :
      MettaCallSync space dispatch (n + 1) atom type_ b (atom, b)
  | grounded_ok (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (nativeResults : ResultSet) (nativeResult : ResultPair)
      (merged : Bindings) (finalResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok nativeResults)
      (h_native_mem : nativeResult ∈ nativeResults)
      (h_merge : merged ∈ mergeBindings nativeResult.2 b n)
      (h_recurse : EvalAtomSync space dispatch n nativeResult.1 type_ merged finalResult) :
      MettaCallSync space dispatch (n + 1) atom type_ b finalResult
  | grounded_runtime_error (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (msg : String)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .runtimeError msg) :
      MettaCallSync space dispatch (n + 1) atom type_ b
        (Atom.error atom (.symbol msg), b)
  | grounded_no_reduce (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .noReduce) :
      MettaCallSync space dispatch (n + 1) atom type_ b (atom, b)
  | grounded_incorrect_arg (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .incorrectArgument) :
      MettaCallSync space dispatch (n + 1) atom type_ b (atom, b)
  | grounded_empty_results (n : Nat) (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok []) :
      MettaCallSync space dispatch (n + 1) atom type_ b (Atom.empty, b)
  | equation_match (n : Nat) (atom type_ : Atom) (b : Bindings)
      (rhs : Atom) (queryBindings merged : Bindings)
      (finalResult : ResultPair)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_query : (rhs, queryBindings) ∈ queryEquations space atom n)
      (h_merge : merged ∈ mergeBindings queryBindings b n)
      (h_no_loop : merged.hasLoop = false)
      (h_recurse : EvalAtomSync space dispatch n (merged.apply rhs n) type_ merged finalResult) :
      MettaCallSync space dispatch (n + 1) atom type_ b finalResult
  | no_match (n : Nat) (atom type_ : Atom) (b : Bindings)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_no_eqs : queryEquations space atom n = []) :
      MettaCallSync space dispatch (n + 1) atom type_ b (atom, b)

end

/-! ### Step 1 foundation lemmas

These are the first exactness-proof helpers:
- evaluator functions normalize to `[]` at fuel `0`,
- synchronous relations are impossible at fuel `0`.

They keep later mutual proofs honest about the shared base case while letting
`simp` clear the zero boundary automatically. -/

@[simp] private theorem evalAtom_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) :
    evalAtom space dispatch atom type_ b 0 = [] := by
  simp [evalAtom]

@[simp] private theorem interpretExpression_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) :
    interpretExpression space dispatch atom type_ b 0 = [] := by
  simp [interpretExpression]

@[simp] private theorem interpretFunction_zero (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) :
    interpretFunction space dispatch atom opType b 0 = [] := by
  simp [interpretFunction]

@[simp] private theorem interpretArgs_zero (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) :
    interpretArgs space dispatch args types b 0 = [] := by
  simp [interpretArgs]

@[simp] private theorem interpretTuple_zero (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) :
    interpretTuple space dispatch atom b 0 = [] := by
  simp [interpretTuple]

@[simp] private theorem mettaCall_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) :
    mettaCall space dispatch atom type_ b 0 = [] := by
  simp [mettaCall]

@[simp] private theorem not_evalAtomSync_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    ¬ EvalAtomSync space dispatch 0 atom type_ b r := by
  intro h
  cases h

@[simp] private theorem not_interpretExpressionSync_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    ¬ InterpretExpressionSync space dispatch 0 atom type_ b r := by
  intro h
  cases h

@[simp] private theorem not_interpretFunctionSync_zero (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) :
    ¬ InterpretFunctionSync space dispatch 0 atom opType b r := by
  intro h
  cases h

@[simp] private theorem not_interpretArgsSync_zero (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) :
    ¬ InterpretArgsSync space dispatch 0 args types b r := by
  intro h
  cases h

@[simp] private theorem not_interpretTupleSync_zero (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) :
    ¬ InterpretTupleSync space dispatch 0 atom b r := by
  intro h
  cases h

@[simp] private theorem not_mettaCallSync_zero (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    ¬ MettaCallSync space dispatch 0 atom type_ b r := by
  intro h
  cases h

/-! ### Step 2 local exactness helpers

These lemmas only target the first exactness frontier:
- successor normal forms for the simpler trio,
- evaluator-to-sync conversion for `interpretArgs`, `interpretTuple`,
  and `interpretFunction`, relative to a supplied `evalAtom` exactness hypothesis.

This keeps the proof load below the harder `evalAtom`/`interpretExpression` frontier. -/

@[simp] private theorem interpretArgs_succ (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (n : Nat) :
    interpretArgs space dispatch args types b (n + 1) =
      match args, types with
      | [], [] => [(Atom.unit, b)]
      | arg :: remainingArgs, t :: remainingTypes =>
        let headResults := evalAtom space dispatch arg t b n
        headResults.flatMap fun (headR, headB) =>
          if headR != arg && isEmptyOrError headR then [(headR, headB)]
          else
            let tailResults :=
              interpretArgs space dispatch remainingArgs remainingTypes headB n
            tailResults.map fun (tailR, tailB) =>
              if isEmptyOrError tailR then (tailR, tailB)
              else (.expression (headR :: atomElements tailR), tailB)
      | _, _ => [] := rfl

@[simp] private theorem interpretTuple_succ (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (n : Nat) :
    interpretTuple space dispatch atom b (n + 1) =
      match atom with
      | .expression [single] =>
        evalAtom space dispatch single Atom.undefinedType b n
      | .expression (hd :: hd2 :: rest) =>
        let headResults := evalAtom space dispatch hd Atom.undefinedType b n
        headResults.flatMap fun (headR, headB) =>
          if isEmptyOrError headR then [(headR, headB)]
          else
            let tailResults :=
              interpretTuple space dispatch (.expression (hd2 :: rest)) headB n
            tailResults.map fun (tailR, tailB) =>
              if isEmptyOrError tailR then (tailR, tailB)
              else (.expression (headR :: atomElements tailR), tailB)
      | _ => [] := rfl

@[simp] private theorem interpretFunction_succ (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (n : Nat) :
    interpretFunction space dispatch atom opType b (n + 1) =
      match atom with
      | .expression (op :: args) =>
        let headResults := evalAtom space dispatch op opType b n
        headResults.flatMap fun (headR, headB) =>
          if isEmptyOrError headR then [(headR, headB)]
          else
            match getFunctionArgTypes opType with
            | some argTypes =>
              let tailResults := interpretArgs space dispatch args argTypes headB n
              tailResults.map fun (tailR, tailB) =>
                if isEmptyOrError tailR then (tailR, tailB)
                else (.expression (headR :: atomElements tailR), tailB)
            | none => []
      | _ => [] := rfl

private theorem interpretArgs_eval_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval : ∀ fuel atom type_ b r,
      r ∈ evalAtom space dispatch atom type_ b fuel →
      EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ fuel args types b r,
      r ∈ interpretArgs space dispatch args types b fuel →
      InterpretArgsSync space dispatch fuel args types b r := by
  intro fuel
  induction fuel with
  | zero =>
      intro args types b r hr
      simp at hr
  | succ n ih =>
      intro args types b r hr
      match args, types with
      | [], [] =>
          simp only [interpretArgs_succ, List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          exact InterpretArgsSync.nil n b
      | arg :: remArgs, t :: remTypes =>
          simp only [interpretArgs_succ, List.mem_flatMap] at hr
          obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
          by_cases h_cond : (headR != arg && isEmptyOrError headR) = true
          · simp [h_cond] at hr2
            subst hr2
            have h_head : EvalAtomSync space dispatch n arg t b (headR, headB) :=
              h_eval n arg t b (headR, headB) h_head_mem
            have h_changed : headR ≠ arg := by
              cases h1 : (headR != arg) <;> cases h2 : isEmptyOrError headR <;>
                simp_all [bne_iff_ne]
            have h_err : isEmptyOrError headR = true := by
              cases h1 : (headR != arg) <;> cases h2 : isEmptyOrError headR <;> simp_all
            exact InterpretArgsSync.head_changed_error n arg remArgs t remTypes b
              (headR, headB) h_head h_err h_changed
          · have h_cond_false : (headR != arg && isEmptyOrError headR) = false := by
              cases h : (headR != arg && isEmptyOrError headR) <;> simp_all
            simp [h_cond_false] at hr2
            have h_head_ok : isEmptyOrError headR = false ∨ headR = arg := by
              cases he : isEmptyOrError headR with
              | false => exact Or.inl rfl
              | true =>
                  right
                  by_contra h_ne
                  have : (headR != arg) = true := by simp [bne_iff_ne, h_ne]
                  simp [this, he] at h_cond
            obtain ⟨tailR, tailB, h_tail_mem, hr3⟩ := hr2
            split at hr3
            · rename_i h_terr
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretArgsSync.cons_tail_error n arg remArgs t remTypes b
                (headR, headB) (tailR, tailB)
                (h_eval n arg t b (headR, headB) h_head_mem) h_head_ok
                (ih remArgs remTypes headB (tailR, tailB) h_tail_mem) h_terr
            · rename_i h_terr_ne
              have h_terr_false : isEmptyOrError tailR = false := by
                cases h : isEmptyOrError tailR <;> simp_all
              subst hr3
              exact InterpretArgsSync.cons_ok n arg remArgs t remTypes b
                (headR, headB) (tailR, tailB)
                (h_eval n arg t b (headR, headB) h_head_mem) h_head_ok
                (ih remArgs remTypes headB (tailR, tailB) h_tail_mem) h_terr_false
      | [], _ :: _ =>
          simp [interpretArgs_succ] at hr
      | _ :: _, [] =>
          simp [interpretArgs_succ] at hr

private theorem interpretTuple_eval_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval : ∀ fuel atom type_ b r,
      r ∈ evalAtom space dispatch atom type_ b fuel →
      EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ fuel atom b r,
      r ∈ interpretTuple space dispatch atom b fuel →
      InterpretTupleSync space dispatch fuel atom b r := by
  intro fuel
  induction fuel with
  | zero =>
      intro atom b r hr
      simp at hr
  | succ n ih =>
      intro atom b r hr
      match atom with
      | .expression [single] =>
          exact InterpretTupleSync.singleton n single b r
            (h_eval n single Atom.undefinedType b r (by simpa [interpretTuple_succ] using hr))
      | .expression (hd :: hd2 :: rest) =>
          simp only [interpretTuple_succ, List.mem_flatMap] at hr
          obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
          split at hr2
          · rename_i h_err
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
            subst hr2
            exact InterpretTupleSync.head_error n hd (hd2 :: rest) b
              (headR, headB) (by simp)
              (h_eval n hd Atom.undefinedType b (headR, headB) h_head_mem) h_err
          · rename_i h_err_ne
            have h_err_false : isEmptyOrError headR = false := by
              cases h : isEmptyOrError headR <;> simp_all
            rw [List.mem_map] at hr2
            obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
            split at hr3
            · rename_i h_terr
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretTupleSync.tail_error n hd (hd2 :: rest) b
                (headR, headB) (tailR, tailB) (by simp)
                (h_eval n hd Atom.undefinedType b (headR, headB) h_head_mem) h_err_false
                (ih (.expression (hd2 :: rest)) headB (tailR, tailB) h_tail_mem) h_terr
            · rename_i h_terr_ne
              have h_terr_false : isEmptyOrError tailR = false := by
                cases h : isEmptyOrError tailR <;> simp_all
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretTupleSync.success n hd (hd2 :: rest) b
                (headR, headB) (tailR, tailB) (by simp)
                (h_eval n hd Atom.undefinedType b (headR, headB) h_head_mem) h_err_false
                (ih (.expression (hd2 :: rest)) headB (tailR, tailB) h_tail_mem) h_terr_false
      | .expression [] =>
          simp [interpretTuple_succ] at hr
      | .symbol _ =>
          simp [interpretTuple_succ] at hr
      | .var _ =>
          simp [interpretTuple_succ] at hr
      | .grounded _ =>
          simp [interpretTuple_succ] at hr

private theorem interpretFunction_eval_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval : ∀ fuel atom type_ b r,
      r ∈ evalAtom space dispatch atom type_ b fuel →
      EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ fuel atom opType b r,
      r ∈ interpretFunction space dispatch atom opType b fuel →
      InterpretFunctionSync space dispatch fuel atom opType b r := by
  intro fuel
  induction fuel with
  | zero =>
      intro atom opType b r hr
      simp at hr
  | succ n ih =>
      intro atom opType b r hr
      match atom with
      | .expression (op :: args) =>
          simp only [interpretFunction_succ, List.mem_flatMap] at hr
          obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
          split at hr2
          · rename_i h_err
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
            subst hr2
            exact InterpretFunctionSync.head_error n (.expression (op :: args)) opType b op args
              (headR, headB) rfl
              (h_eval n op opType b (headR, headB) h_head_mem) h_err
          · rename_i h_err_ne
            have h_err_false : isEmptyOrError headR = false := by
              cases h : isEmptyOrError headR <;> simp_all
            match h_argt : getFunctionArgTypes opType with
            | some argTypes =>
                simp only [h_argt] at hr2
                rw [List.mem_map] at hr2
                obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
                split at hr3
                · rename_i h_terr
                  obtain ⟨rfl, rfl⟩ := hr3
                  exact InterpretFunctionSync.head_ok_tail_error n (.expression (op :: args)) opType b
                    op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                    (h_eval n op opType b (headR, headB) h_head_mem) h_err_false
                    (interpretArgs_eval_to_sync space dispatch h_eval n args argTypes headB
                      (tailR, tailB) h_tail_mem) h_terr
                · rename_i h_terr_ne
                  have h_terr_false : isEmptyOrError tailR = false := by
                    cases h : isEmptyOrError tailR <;> simp_all
                  obtain ⟨rfl, rfl⟩ := hr3
                  exact InterpretFunctionSync.head_ok_tail_ok n (.expression (op :: args)) opType b
                    op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                    (h_eval n op opType b (headR, headB) h_head_mem) h_err_false
                    (interpretArgs_eval_to_sync space dispatch h_eval n args argTypes headB
                      (tailR, tailB) h_tail_mem) h_terr_false
            | none =>
                simp only [h_argt, List.not_mem_nil] at hr2
      | .symbol _ =>
          simp [interpretFunction_succ] at hr
      | .var _ =>
          simp [interpretFunction_succ] at hr
      | .grounded _ =>
          simp [interpretFunction_succ] at hr
      | .expression [] =>
          simp [interpretFunction_succ] at hr

/-! ### Step 3 exactness bundle targets

These structures define the bounded theorem surface we now care about:
- sync derivation implies evaluator membership at the same fuel,
- evaluator membership implies sync derivation at the same fuel.

They keep the remaining exactness work bundled and prevent theorem sprawl. -/

private structure AllSyncToEval (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) : Prop where
  evalAtom :
    ∀ atom type_ b r,
      EvalAtomSync space dispatch fuel atom type_ b r →
      r ∈ evalAtom space dispatch atom type_ b fuel
  interpretExpression :
    ∀ atom type_ b r,
      InterpretExpressionSync space dispatch fuel atom type_ b r →
      r ∈ interpretExpression space dispatch atom type_ b fuel
  interpretFunction :
    ∀ atom opType b r,
      InterpretFunctionSync space dispatch fuel atom opType b r →
      r ∈ interpretFunction space dispatch atom opType b fuel
  interpretArgs :
    ∀ args types b r,
      InterpretArgsSync space dispatch fuel args types b r →
      r ∈ interpretArgs space dispatch args types b fuel
  interpretTuple :
    ∀ atom b r,
      InterpretTupleSync space dispatch fuel atom b r →
      r ∈ interpretTuple space dispatch atom b fuel
  mettaCall :
    ∀ atom type_ b r,
      MettaCallSync space dispatch fuel atom type_ b r →
      r ∈ mettaCall space dispatch atom type_ b fuel

private structure AllEvalToSync (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) : Prop where
  evalAtom :
    ∀ atom type_ b r,
      r ∈ evalAtom space dispatch atom type_ b fuel →
      EvalAtomSync space dispatch fuel atom type_ b r
  interpretExpression :
    ∀ atom type_ b r,
      r ∈ interpretExpression space dispatch atom type_ b fuel →
      InterpretExpressionSync space dispatch fuel atom type_ b r
  interpretFunction :
    ∀ atom opType b r,
      r ∈ interpretFunction space dispatch atom opType b fuel →
      InterpretFunctionSync space dispatch fuel atom opType b r
  interpretArgs :
    ∀ args types b r,
      r ∈ interpretArgs space dispatch args types b fuel →
      InterpretArgsSync space dispatch fuel args types b r
  interpretTuple :
    ∀ atom b r,
      r ∈ interpretTuple space dispatch atom b fuel →
      InterpretTupleSync space dispatch fuel atom b r
  mettaCall :
    ∀ atom type_ b r,
      r ∈ mettaCall space dispatch atom type_ b fuel →
      MettaCallSync space dispatch fuel atom type_ b r

private theorem allEvalToSync_zero (space : Space) (dispatch : GroundedDispatch) :
    AllEvalToSync space dispatch 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro atom type_ b r hr
    simp at hr
  · intro atom type_ b r hr
    simp at hr
  · intro atom opType b r hr
    simp at hr
  · intro args types b r hr
    simp at hr
  · intro atom b r hr
    simp at hr
  · intro atom type_ b r hr
    simp at hr

/-! ### Step 4 sync-to-evaluator exactness bundle

The first half of exactness is proved by induction on the shared evaluator fuel.
This mirrors the successful `AllSound` organization above and keeps the proof
surface bounded to one private bundle instead of a growing forest of ad hoc
helper lemmas. -/

private theorem isEmpty_false_of_mem {α : Type*} {xs : List α} {x : α}
    (hx : x ∈ xs) : xs.isEmpty = false := by
  cases xs with
  | nil => simp at hx
  | cons _ _ => simp

private theorem mem_nonerror_filter {results : ResultSet} {r : ResultPair}
    (hr : r ∈ results) (h_not_error : isErrorAtom r.1 = false) :
    r ∈ List.filter (fun x => !isErrorAtom x.1) results := by
  rw [List.mem_filter]
  exact ⟨hr, by simp [h_not_error]⟩

private theorem mem_error_filter {results : ResultSet} {r : ResultPair}
    (hr : r ∈ results) (h_is_error : isErrorAtom r.1 = true) :
    r ∈ List.filter (fun x => isErrorAtom x.1) results := by
  rw [List.mem_filter]
  exact ⟨hr, h_is_error⟩

private theorem nonerror_filter_isEmpty_true_of_onlyErrors {results : ResultSet}
    (h_all : OnlyErrorsAt results) :
    (List.filter (fun x => !isErrorAtom x.1) results).isEmpty = true := by
  cases hres : List.filter (fun x => !isErrorAtom x.1) results with
  | nil =>
      simp
  | cons x xs =>
      have hx_mem : x ∈ List.filter (fun x => !isErrorAtom x.1) results := by
        simp [hres]
      rw [List.mem_filter] at hx_mem
      have hx_err : isErrorAtom x.1 = true := h_all x hx_mem.1
      simp [hx_err] at hx_mem

private theorem allSyncToEval_zero (space : Space) (dispatch : GroundedDispatch) :
    AllSyncToEval space dispatch 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro atom type_ b r h
    cases h
  · intro atom type_ b r h
    cases h
  · intro atom opType b r h
    cases h
  · intro args types b r h
    cases h
  · intro atom b r h
    cases h
  · intro atom type_ b r h
    cases h

private theorem interpretArgs_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ args types b r,
      InterpretArgsSync space dispatch (n + 1) args types b r →
      r ∈ interpretArgs space dispatch args types b (n + 1) := by
  intro args types b r h
  cases h with
  | nil _ b =>
      simp [interpretArgs_succ]
  | head_changed_error _ a as t ts b headResult h_head h_err h_changed =>
      rw [interpretArgs_succ]
      rw [List.mem_flatMap]
      refine ⟨r, ih.evalAtom _ _ _ _ h_head, ?_⟩
      simp [h_err, h_changed, bne_iff_ne]
  | cons_tail_error _ a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_err =>
      rw [interpretArgs_succ]
      rw [List.mem_flatMap]
      refine ⟨headResult, ih.evalAtom _ _ _ _ h_head, ?_⟩
      have h_cond_false : (headResult.1 != a && isEmptyOrError headResult.1) = false := by
        rcases h_head_ok with h_ok | h_same
        · simp [h_ok]
        · simp [h_same]
      simp [h_cond_false]
      refine ⟨r.1, r.2, ih.interpretArgs _ _ _ _ h_tail, ?_⟩
      simp [h_tail_err]
  | cons_ok _ a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_ok =>
      rw [interpretArgs_succ]
      rw [List.mem_flatMap]
      refine ⟨headResult, ih.evalAtom _ _ _ _ h_head, ?_⟩
      have h_cond_false : (headResult.1 != a && isEmptyOrError headResult.1) = false := by
        rcases h_head_ok with h_ok | h_same
        · simp [h_ok]
        · simp [h_same]
      simp [h_cond_false]
      refine ⟨tailResult.1, tailResult.2, ih.interpretArgs _ _ _ _ h_tail, ?_⟩
      simp [h_tail_ok]

private theorem interpretFunction_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ atom opType b r,
      InterpretFunctionSync space dispatch (n + 1) atom opType b r →
      r ∈ interpretFunction space dispatch atom opType b (n + 1) := by
  intro atom opType b r h
  cases h with
  | head_error _ atom opType b op args headResult h_shape h_head h_err =>
      subst h_shape
      simp [interpretFunction_succ]
      refine ⟨r.1, r.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
      simp [h_err]
  | head_ok_tail_error _ atom opType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_err =>
      subst h_shape
      simp [interpretFunction_succ]
      refine ⟨headResult.1, headResult.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
      simp [h_head_ok, h_arg_types]
      refine ⟨r.1, r.2, ih.interpretArgs _ _ _ _ h_tail, ?_⟩
      simp [h_tail_err]
  | head_ok_tail_ok _ atom opType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_ok =>
      subst h_shape
      simp [interpretFunction_succ]
      refine ⟨headResult.1, headResult.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
      simp [h_head_ok, h_arg_types]
      refine ⟨tailResult.1, tailResult.2, ih.interpretArgs _ _ _ _ h_tail, ?_⟩
      simp [h_tail_ok]

private theorem interpretTuple_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ atom b r,
      InterpretTupleSync space dispatch (n + 1) atom b r →
      r ∈ interpretTuple space dispatch atom b (n + 1) := by
  intro atom b r h
  cases h with
  | singleton _ a b r h_eval =>
      simpa [interpretTuple_succ] using ih.evalAtom a Atom.undefinedType b r h_eval
  | head_error _ hd tl b headResult h_tl_nonempty h_head h_err =>
      cases tl with
      | nil =>
          contradiction
      | cons hd2 rest =>
          simp [interpretTuple_succ]
          refine ⟨r.1, r.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
          simp [h_err]
  | tail_error _ hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
      cases tl with
      | nil =>
          contradiction
      | cons hd2 rest =>
          simp [interpretTuple_succ]
          refine ⟨headResult.1, headResult.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
          simp [h_head_ok]
          refine ⟨r.1, r.2, ih.interpretTuple _ _ _ h_tail, ?_⟩
          simp [h_tail_err]
  | success _ hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
      cases tl with
      | nil =>
          contradiction
      | cons hd2 rest =>
          simp [interpretTuple_succ]
          refine ⟨headResult.1, headResult.2, ih.evalAtom _ _ _ _ h_head, ?_⟩
          simp [h_head_ok]
          refine ⟨tailResult.1, tailResult.2, ih.interpretTuple _ _ _ h_tail, ?_⟩
          simp [h_tail_ok]

private theorem mettaCall_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ atom type_ b r,
      MettaCallSync space dispatch (n + 1) atom type_ b r →
      r ∈ mettaCall space dispatch atom type_ b (n + 1) := by
  intro atom type_ b r h
  cases h with
  | error_passthrough _ atom type_ b h_err =>
      simp [mettaCall, h_err]
  | grounded_ok _ atom type_ b op args nativeResults nativeResult merged finalResult
      h_shape h_exec h_not_error h_native h_native_mem h_merge h_recurse =>
      subst h_shape
      have h_native_nonempty : nativeResults.isEmpty = false :=
        isEmpty_false_of_mem h_native_mem
      simp [mettaCall, h_not_error, h_exec, h_native, h_native_nonempty]
      refine ⟨nativeResult.1, nativeResult.2, h_native_mem, merged, h_merge, ?_⟩
      exact ih.evalAtom _ _ _ _ h_recurse
  | grounded_runtime_error _ atom type_ b op args msg h_shape h_exec h_not_error h_native =>
      subst h_shape
      simp [mettaCall, h_not_error, h_exec, h_native]
  | grounded_no_reduce _ atom type_ b op args h_shape h_exec h_not_error h_native =>
      subst h_shape
      simp [mettaCall, h_not_error, h_exec, h_native]
  | grounded_incorrect_arg _ atom type_ b op args h_shape h_exec h_not_error h_native =>
      subst h_shape
      simp [mettaCall, h_not_error, h_exec, h_native]
  | grounded_empty_results _ atom type_ b op args h_shape h_exec h_not_error h_native =>
      subst h_shape
      simp [mettaCall, h_not_error, h_exec, h_native]
  | equation_match _ atom type_ b rhs queryBindings merged finalResult h_not_error
      h_not_grounded h_query h_merge h_no_loop h_recurse =>
      cases atom with
      | symbol s =>
          have h_eqs_nonempty : (queryEquations space (.symbol s) n).isEmpty = false :=
            isEmpty_false_of_mem h_query
          simp [mettaCall, h_not_error, h_eqs_nonempty]
          refine ⟨rhs, queryBindings, h_query, merged, h_merge, h_no_loop, ?_⟩
          exact ih.evalAtom _ _ _ _ h_recurse
      | var v =>
          have h_eqs_nonempty : (queryEquations space (.var v) n).isEmpty = false :=
            isEmpty_false_of_mem h_query
          simp [mettaCall, h_not_error, h_eqs_nonempty]
          refine ⟨rhs, queryBindings, h_query, merged, h_merge, h_no_loop, ?_⟩
          exact ih.evalAtom _ _ _ _ h_recurse
      | grounded g =>
          have h_eqs_nonempty : (queryEquations space (.grounded g) n).isEmpty = false :=
            isEmpty_false_of_mem h_query
          simp [mettaCall, h_not_error, h_eqs_nonempty]
          refine ⟨rhs, queryBindings, h_query, merged, h_merge, h_no_loop, ?_⟩
          exact ih.evalAtom _ _ _ _ h_recurse
      | expression es =>
          cases es with
          | nil =>
              have h_eqs_nonempty : (queryEquations space (.expression []) n).isEmpty = false :=
                isEmpty_false_of_mem h_query
              simp [mettaCall, h_not_error, h_eqs_nonempty]
              refine ⟨rhs, queryBindings, h_query, merged, h_merge, h_no_loop, ?_⟩
              exact ih.evalAtom _ _ _ _ h_recurse
          | cons op args =>
              have h_eqs_nonempty :
                  (queryEquations space (.expression (op :: args)) n).isEmpty = false :=
                isEmpty_false_of_mem h_query
              simp [mettaCall, h_not_error, h_not_grounded, h_eqs_nonempty]
              refine ⟨rhs, queryBindings, h_query, merged, h_merge, h_no_loop, ?_⟩
              exact ih.evalAtom _ _ _ _ h_recurse
  | no_match _ atom type_ b h_not_error h_not_grounded h_no_eqs =>
      cases atom with
      | symbol s =>
          simp [mettaCall, h_not_error, h_no_eqs]
      | var v =>
          simp [mettaCall, h_not_error, h_no_eqs]
      | grounded g =>
          simp [mettaCall, h_not_error, h_no_eqs]
      | expression es =>
          cases es with
          | nil =>
              simp [mettaCall, h_not_error, h_no_eqs]
          | cons op args =>
              simp [mettaCall, h_not_error, h_not_grounded, h_no_eqs]

private theorem interpretExpression_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ atom type_ b r,
      InterpretExpressionSync space dispatch (n + 1) atom type_ b r →
      r ∈ interpretExpression space dispatch atom type_ b (n + 1) := by
  intro atom type_ b r h
  cases h with
  | function_path _ atom type_ b op args funcType b' interpResult callResult succs
      h_shape h_op_type h_is_func h_check h_check_b h_interp h_call =>
      subst h_shape
      let retType :=
        if getFunctionRetType funcType == some Atom.expressionType
        then Atom.undefinedType
        else (getFunctionRetType funcType).getD Atom.undefinedType
      have h_interp_mem :
          interpResult ∈ interpretFunction space dispatch (.expression (op :: args)) funcType b' n :=
        ih.interpretFunction _ _ _ _ h_interp
      have h_call_mem :
          r ∈ mettaCall space dispatch interpResult.1 retType interpResult.2 n := by
        exact ih.mettaCall _ _ _ _ h_call
      have h_func_mem :
          r ∈
            (getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else [] := by
        rw [List.mem_flatMap]
        refine ⟨funcType, h_op_type, ?_⟩
        simp [h_is_func, h_check]
        refine ⟨b', h_check_b, interpResult.1, interpResult.2, h_interp_mem, ?_⟩
        simpa [retType] using h_call_mem
      have h_all_mem :
          r ∈
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        exact List.mem_append.mpr <| Or.inl h_func_mem
      have h_all_mem_prop :
          r ∈
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        by_cases h_has_non_func_prop :
            ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType
        · have h_has_non_func :
              ((getAtomTypes space op).any fun t => !isFunctionType t || t == Atom.undefinedType) = true := by
            simpa [List.any_eq_true] using h_has_non_func_prop
          simpa [h_has_non_func, h_has_non_func_prop, List.any_eq_true] using h_all_mem
        · have h_has_non_func :
              ((getAtomTypes space op).any fun t => !isFunctionType t || t == Atom.undefinedType) = false := by
            by_cases h_bool :
                ((getAtomTypes space op).any fun t => !isFunctionType t || t == Atom.undefinedType) = true
            · have : ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType := by
                simpa [List.any_eq_true] using h_bool
              exact (h_has_non_func_prop this).elim
            · cases h_any : ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) <;> simp_all
          simpa [h_has_non_func, h_has_non_func_prop, List.any_eq_true] using h_all_mem
      have h_outer_false :
          (((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else [])).isEmpty = false :=
        isEmpty_false_of_mem h_all_mem
      have h_outer_true :
          (!List.isEmpty
              (((getAtomTypes space op).flatMap fun ft =>
                  if isFunctionType ft then
                    match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                    | .inr succs =>
                      succs.flatMap fun b'' =>
                        let retType :=
                          if getFunctionRetType ft == some Atom.expressionType
                          then Atom.undefinedType
                          else (getFunctionRetType ft).getD Atom.undefinedType
                        let interpResults :=
                          interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                        interpResults.flatMap fun (r', rb) =>
                          mettaCall space dispatch r' retType rb n
                    | .inl _ => []
                  else []) ++
                (if ((getAtomTypes space op).any fun t =>
                      !isFunctionType t || t == Atom.undefinedType) then
                  let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
                  interpResults.flatMap fun (r', rb) =>
                    mettaCall space dispatch r' type_ rb n
                 else []))) = true := by
        simpa using congrArg (!·) h_outer_false
      have h_outer_true_target :
          (!List.isEmpty
              (((getAtomTypes space op).flatMap fun funcType =>
                  if isFunctionType funcType then
                    match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
                    | .inr succs =>
                      succs.flatMap fun b' =>
                        (interpretFunction space dispatch (.expression (op :: args)) funcType b' n).flatMap
                          fun x =>
                            mettaCall space dispatch x.1
                              (if (getFunctionRetType funcType == some Atom.expressionType) = true
                               then Atom.undefinedType
                               else (getFunctionRetType funcType).getD Atom.undefinedType)
                              x.2 n
                    | .inl _ => []
                  else []) ++
                (if ((getAtomTypes space op).any fun t =>
                      !isFunctionType t || t == Atom.undefinedType) = true then
                  (interpretTuple space dispatch (.expression (op :: args)) b n).flatMap
                    fun x => mettaCall space dispatch x.1 type_ x.2 n
                 else []))) = true := by
        simpa using h_outer_true
      have h_eval :
          interpretExpression space dispatch (.expression (op :: args)) type_ b (n + 1) =
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        simp [interpretExpression, List.any_eq_true]
        refine (if_pos h_outer_true_target).trans ?_
        by_cases h_nf : ((getAtomTypes space op).any fun t =>
            !isFunctionType t || t == Atom.undefinedType) = true
        · have h_nf_prop :
              ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType := by
            simpa [List.any_eq_true] using h_nf
          rfl
        · have h_nf_prop :
              ¬ ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType := by
            intro hex
            exact h_nf (by simpa [List.any_eq_true] using hex)
          rfl
      rw [h_eval]
      exact h_all_mem_prop
  | tuple_path _ atom type_ b op args tupleResult callResult
      h_shape h_has_non_func h_tuple h_call =>
      subst h_shape
      have h_tuple_mem :
          tupleResult ∈ interpretTuple space dispatch (.expression (op :: args)) b n :=
        ih.interpretTuple _ _ _ h_tuple
      have h_call_mem :
          r ∈ mettaCall space dispatch tupleResult.1 type_ tupleResult.2 n := by
        exact ih.mettaCall _ _ _ _ h_call
      have h_tuple_path_mem :
          r ∈
            (if ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        simp [h_has_non_func]
        exact ⟨tupleResult.1, tupleResult.2, h_tuple_mem, h_call_mem⟩
      have h_all_mem :
          r ∈
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        exact List.mem_append.mpr <| Or.inr h_tuple_path_mem
      have h_has_non_func_prop :
          ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType := by
        simpa [List.any_eq_true] using h_has_non_func
      have h_all_mem_prop :
          r ∈
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        simpa [h_has_non_func, h_has_non_func_prop, List.any_eq_true] using h_all_mem
      have h_outer_false :
          (((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else [])).isEmpty = false :=
        isEmpty_false_of_mem h_all_mem
      have h_outer_true :
          (!List.isEmpty
              (((getAtomTypes space op).flatMap fun ft =>
                  if isFunctionType ft then
                    match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                    | .inr succs =>
                      succs.flatMap fun b'' =>
                        let retType :=
                          if getFunctionRetType ft == some Atom.expressionType
                          then Atom.undefinedType
                          else (getFunctionRetType ft).getD Atom.undefinedType
                        let interpResults :=
                          interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                        interpResults.flatMap fun (r', rb) =>
                          mettaCall space dispatch r' retType rb n
                    | .inl _ => []
                  else []) ++
                (if ((getAtomTypes space op).any fun t =>
                      !isFunctionType t || t == Atom.undefinedType) then
                  let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
                  interpResults.flatMap fun (r', rb) =>
                    mettaCall space dispatch r' type_ rb n
                 else []))) = true := by
        simpa using congrArg (!·) h_outer_false
      have h_outer_true_target :
          (!List.isEmpty
              (((getAtomTypes space op).flatMap fun funcType =>
                  if isFunctionType funcType then
                    match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
                    | .inr succs =>
                      succs.flatMap fun b' =>
                        (interpretFunction space dispatch (.expression (op :: args)) funcType b' n).flatMap
                          fun x =>
                            mettaCall space dispatch x.1
                              (if (getFunctionRetType funcType == some Atom.expressionType) = true
                               then Atom.undefinedType
                               else (getFunctionRetType funcType).getD Atom.undefinedType)
                              x.2 n
                    | .inl _ => []
                  else []) ++
                (if ((getAtomTypes space op).any fun t =>
                      !isFunctionType t || t == Atom.undefinedType) = true then
                  (interpretTuple space dispatch (.expression (op :: args)) b n).flatMap
                    fun x => mettaCall space dispatch x.1 type_ x.2 n
                 else []))) = true := by
        simpa using h_outer_true
      have h_eval :
          interpretExpression space dispatch (.expression (op :: args)) type_ b (n + 1) =
            ((getAtomTypes space op).flatMap fun ft =>
              if isFunctionType ft then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
                | .inr succs =>
                  succs.flatMap fun b'' =>
                    let retType :=
                      if getFunctionRetType ft == some Atom.expressionType
                      then Atom.undefinedType
                      else (getFunctionRetType ft).getD Atom.undefinedType
                    let interpResults :=
                      interpretFunction space dispatch (.expression (op :: args)) ft b'' n
                    interpResults.flatMap fun (r', rb) =>
                      mettaCall space dispatch r' retType rb n
                | .inl _ => []
              else []) ++
            (if ∃ x ∈ getAtomTypes space op, isFunctionType x = false ∨ x = Atom.undefinedType then
              let interpResults := interpretTuple space dispatch (.expression (op :: args)) b n
              interpResults.flatMap fun (r', rb) =>
                mettaCall space dispatch r' type_ rb n
             else []) := by
        simp [interpretExpression, h_has_non_func]
        refine (if_pos h_outer_true_target).trans ?_
        simp [h_has_non_func_prop]
        rfl
      rw [h_eval]
      exact h_all_mem_prop
  | op_type_error _ atom type_ b op args failedType errs errAtom
      h_shape h_has_non_func h_all_fail h_failed_type h_failed_func h_check_fail h_err_mem =>
      subst h_shape
      have h_no_func_success :
          ¬ ∃ x ∈ getAtomTypes space op,
              isFunctionType x = true ∧
                ¬(match checkIfFunctionTypeIsApplicable (.expression (op :: args)) x type_ space b n with
                  | .inr succs =>
                    succs.flatMap fun b' =>
                      let retType :=
                        if getFunctionRetType x == some Atom.expressionType
                        then Atom.undefinedType
                        else (getFunctionRetType x).getD Atom.undefinedType
                      let interpResults :=
                        interpretFunction space dispatch (.expression (op :: args)) x b' n
                      interpResults.flatMap fun (r', rb) =>
                        mettaCall space dispatch r' retType rb n
                  | .inl _ => []) = [] := by
        intro hex
        rcases hex with ⟨ft, h_ft_mem, h_ft_func, h_nonempty⟩
        have h_all_ft : (if isFunctionType ft then
            match checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
            | .inl _ => true
            | .inr _ => false
          else true) = true := by
          rw [List.all_eq_true] at h_all_fail
          exact h_all_fail ft h_ft_mem
        simp [h_ft_func] at h_all_ft
        cases h_chk : checkIfFunctionTypeIsApplicable (.expression (op :: args)) ft type_ space b n with
        | inl errs' =>
            simp [h_chk] at h_nonempty
        | inr succs =>
            simp [h_chk] at h_all_ft
      have h_all_fail_prop :
          ∀ x ∈ getAtomTypes space op,
            isFunctionType x = false ∨
              (match checkIfFunctionTypeIsApplicable (.expression (op :: args)) x type_ space b n with
                | .inl _ => true
                | .inr _ => false) = true := by
        rw [List.all_eq_true] at h_all_fail
        intro x hx
        have hx_all := h_all_fail x hx
        cases h_func : isFunctionType x with
        | false =>
            exact Or.inl rfl
        | true =>
            exact Or.inr (by simpa [h_func] using hx_all)
      have h_err_list_mem :
          (errAtom, b) ∈
            (getAtomTypes space op).flatMap fun funcType =>
              if isFunctionType funcType then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
                | .inl errs => errs.map fun e => (e, b)
                | .inr _ => []
              else [] := by
        rw [List.mem_flatMap]
        refine ⟨failedType, h_failed_type, ?_⟩
        simp [h_failed_func, h_check_fail, h_err_mem]
      have h_no_func_success_target :
          ¬ ∃ x ∈ getAtomTypes space op,
              isFunctionType x = true ∧
                ¬(match checkIfFunctionTypeIsApplicable (.expression (op :: args)) x type_ space b n with
                  | .inr succs =>
                    succs.flatMap fun b' =>
                      (interpretFunction space dispatch (.expression (op :: args)) x b' n).flatMap
                        fun x_1 =>
                          mettaCall space dispatch x_1.1
                            (if getFunctionRetType x = some Atom.expressionType
                             then Atom.undefinedType
                             else (getFunctionRetType x).getD Atom.undefinedType)
                            x_1.2 n
                  | .inl _ => []) = [] := by
        simpa using h_no_func_success
      have h_eval :
          interpretExpression space dispatch (.expression (op :: args)) type_ b (n + 1) =
            (getAtomTypes space op).flatMap fun funcType =>
              if isFunctionType funcType then
                match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
                | .inl errs => errs.map fun e => (e, b)
                | .inr _ => []
              else [] := by
        simp [interpretExpression, h_has_non_func]
        refine (if_neg h_no_func_success_target).trans ?_
        exact if_pos h_all_fail_prop
      rw [h_eval]
      exact h_err_list_mem

private theorem evalAtom_sync_to_eval_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    ∀ atom type_ b r,
      EvalAtomSync space dispatch (n + 1) atom type_ b r →
      r ∈ evalAtom space dispatch atom type_ b (n + 1) := by
  intro atom type_ b r h
  cases h with
  | empty_or_error _ atom type_ b h_empty =>
      simp [evalAtom, h_empty]
  | type_pass _ atom type_ b h_not_empty h_pass =>
      have h_pass_bool :
          (type_ == Atom.atomType
            || type_ == getMetaType atom
            || getMetaType atom == Atom.variableType) = true := by
        rcases h_pass with h_atom | h_meta | h_var
        · simp [h_atom]
        · simp [h_meta]
        · simp [h_var]
      simp [evalAtom, h_not_empty, h_pass_bool]
  | type_cast _ atom type_ b r h_not_empty h_not_pass h_cast_branch h_result =>
      have h_pass_false :
          (type_ == Atom.atomType
            || type_ == getMetaType atom
            || getMetaType atom == Atom.variableType) = false := by
        by_cases h_atom : type_ == Atom.atomType
        · exact (h_not_pass <| Or.inl (eq_of_beq h_atom)).elim
        · by_cases h_meta : type_ == getMetaType atom
          · exact (h_not_pass <| Or.inr <| Or.inl (eq_of_beq h_meta)).elim
          · by_cases h_var : getMetaType atom == Atom.variableType
            · exact (h_not_pass <| Or.inr <| Or.inr (eq_of_beq h_var)).elim
            · simp [h_atom, h_meta, h_var]
      have h_cast_bool :
          (getMetaType atom == Atom.symbolType
            || getMetaType atom == Atom.groundedType
            || atom == Atom.unit) = true := by
        rcases h_cast_branch with h_sym | h_grounded | h_unit
        · simp [h_sym]
        · simp [h_grounded]
        · simp [h_unit]
      simpa [evalAtom, h_not_empty, h_pass_false, h_cast_bool] using h_result
  | interpret_success _ atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp
      h_not_error =>
      have h_pass_false :
          (type_ == Atom.atomType
            || type_ == getMetaType atom
            || getMetaType atom == Atom.variableType) = false := by
        by_cases h_atom : type_ == Atom.atomType
        · exact (h_not_pass <| Or.inl (eq_of_beq h_atom)).elim
        · by_cases h_meta : type_ == getMetaType atom
          · exact (h_not_pass <| Or.inr <| Or.inl (eq_of_beq h_meta)).elim
          · by_cases h_var : getMetaType atom == Atom.variableType
            · exact (h_not_pass <| Or.inr <| Or.inr (eq_of_beq h_var)).elim
            · simp [h_atom, h_meta, h_var]
      have h_cast_false :
          (getMetaType atom == Atom.symbolType
            || getMetaType atom == Atom.groundedType
            || atom == Atom.unit) = false := by
        have h_ne_sym : Atom.expressionType ≠ Atom.symbolType := by native_decide
        have h_ne_grounded : Atom.expressionType ≠ Atom.groundedType := by native_decide
        simp [h_expr, h_not_unit, h_ne_sym, h_ne_grounded]
      have h_expr_true : getMetaType atom == Atom.expressionType := by
        simp [h_expr]
      have h_interp_mem :
          r ∈ interpretExpression space dispatch atom type_ b n :=
        ih.interpretExpression _ _ _ _ h_interp
      have h_success_mem :
          r ∈ (interpretExpression space dispatch atom type_ b n).filter
            (fun x => !isErrorAtom x.1) :=
        mem_nonerror_filter h_interp_mem h_not_error
      have h_successes_nonempty :
          ((interpretExpression space dispatch atom type_ b n).filter
            (fun x => !isErrorAtom x.1)).isEmpty = false :=
        isEmpty_false_of_mem h_success_mem
      have h_successes_taken :
          (!((interpretExpression space dispatch atom type_ b n).filter
              (fun x => !isErrorAtom x.1)).isEmpty) = true := by
        simpa using congrArg (!·) h_successes_nonempty
      simpa [evalAtom, h_not_empty, h_pass_false, h_cast_false, h_expr_true,
        h_successes_taken] using h_success_mem
  | interpret_error _ atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp
      h_is_error h_all_errors =>
      have h_pass_false :
          (type_ == Atom.atomType
            || type_ == getMetaType atom
            || getMetaType atom == Atom.variableType) = false := by
        by_cases h_atom : type_ == Atom.atomType
        · exact (h_not_pass <| Or.inl (eq_of_beq h_atom)).elim
        · by_cases h_meta : type_ == getMetaType atom
          · exact (h_not_pass <| Or.inr <| Or.inl (eq_of_beq h_meta)).elim
          · by_cases h_var : getMetaType atom == Atom.variableType
            · exact (h_not_pass <| Or.inr <| Or.inr (eq_of_beq h_var)).elim
            · simp [h_atom, h_meta, h_var]
      have h_cast_false :
          (getMetaType atom == Atom.symbolType
            || getMetaType atom == Atom.groundedType
            || atom == Atom.unit) = false := by
        have h_ne_sym : Atom.expressionType ≠ Atom.symbolType := by native_decide
        have h_ne_grounded : Atom.expressionType ≠ Atom.groundedType := by native_decide
        simp [h_expr, h_not_unit, h_ne_sym, h_ne_grounded]
      have h_expr_true : getMetaType atom == Atom.expressionType := by
        simp [h_expr]
      have h_interp_mem :
          r ∈ interpretExpression space dispatch atom type_ b n :=
        ih.interpretExpression _ _ _ _ h_interp
      have h_error_mem :
          r ∈ (interpretExpression space dispatch atom type_ b n).filter
            (fun x => isErrorAtom x.1) :=
        mem_error_filter h_interp_mem h_is_error
      have h_successes_empty :
          ((interpretExpression space dispatch atom type_ b n).filter
            (fun x => !isErrorAtom x.1)).isEmpty = true :=
        nonerror_filter_isEmpty_true_of_onlyErrors h_all_errors
      have h_successes_dropped :
          (!((interpretExpression space dispatch atom type_ b n).filter
              (fun x => !isErrorAtom x.1)).isEmpty) = false := by
        simp [h_successes_empty]
      simpa [evalAtom, h_not_empty, h_pass_false, h_cast_false, h_expr_true,
        h_successes_dropped] using h_error_mem

private theorem allSyncToEval_succ
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllSyncToEval space dispatch n) :
    AllSyncToEval space dispatch (n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact evalAtom_sync_to_eval_step space dispatch n ih
  · exact interpretExpression_sync_to_eval_step space dispatch n ih
  · exact interpretFunction_sync_to_eval_step space dispatch n ih
  · exact interpretArgs_sync_to_eval_step space dispatch n ih
  · exact interpretTuple_sync_to_eval_step space dispatch n ih
  · exact mettaCall_sync_to_eval_step space dispatch n ih

private theorem allSyncToEval
    (space : Space) (dispatch : GroundedDispatch) :
    ∀ fuel, AllSyncToEval space dispatch fuel
  | 0 => allSyncToEval_zero space dispatch
  | n + 1 => allSyncToEval_succ space dispatch n (allSyncToEval space dispatch n)

/-! ### Step 5 sync-to-canonical refinement via evaluator soundness

Once sync-to-evaluator exactness is bundled, refinement to the canonical HE
semantics is just composition with the already-proved soundness theorems. -/

private theorem evalAtomSync_to_EvalAtom
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
    (h : EvalAtomSync space dispatch fuel atom type_ b r) :
    EvalAtom space dispatch atom type_ b r :=
  evalAtom_sound space dispatch atom type_ b fuel r
    ((allSyncToEval space dispatch fuel).evalAtom atom type_ b r h)

private theorem interpretExpressionSync_to_InterpretExpression
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
    (h : InterpretExpressionSync space dispatch fuel atom type_ b r) :
    InterpretExpression space dispatch atom type_ b r :=
  interpretExpression_sound space dispatch atom type_ b fuel r
    ((allSyncToEval space dispatch fuel).interpretExpression atom type_ b r h)

private theorem interpretFunctionSync_to_InterpretFunction
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom opType : Atom) (b : Bindings) (r : ResultPair) :
    InterpretFunctionSync space dispatch fuel atom opType b r →
    ∀ retType, InterpretFunction space dispatch atom opType retType b r := by
  intro h retType
  exact interpretFunction_sound space dispatch atom opType b fuel r
    ((allSyncToEval space dispatch fuel).interpretFunction atom opType b r h)
    retType

private theorem interpretArgsSync_to_InterpretArgs
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (args types : List Atom) (b : Bindings) (r : ResultPair)
    (h : InterpretArgsSync space dispatch fuel args types b r) :
    InterpretArgs space dispatch args types b r :=
  interpretArgs_sound space dispatch args types b fuel r
    ((allSyncToEval space dispatch fuel).interpretArgs args types b r h)

private theorem interpretTupleSync_to_InterpretTuple
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom : Atom) (b : Bindings) (r : ResultPair)
    (h : InterpretTupleSync space dispatch fuel atom b r) :
    InterpretTuple space dispatch atom b r :=
  interpretTuple_sound space dispatch atom b fuel r
    ((allSyncToEval space dispatch fuel).interpretTuple atom b r h)

private theorem mettaCallSync_to_MettaCall
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair)
    (h : MettaCallSync space dispatch fuel atom type_ b r) :
    MettaCall space dispatch atom type_ b r :=
  mettaCall_sound space dispatch atom type_ b fuel r
    ((allSyncToEval space dispatch fuel).mettaCall atom type_ b r h)

/-! ### Step 6 evaluator-to-sync step lemmas

The reverse direction now follows the same fuel-step pattern as the successful
forward bundle, rather than relying on the earlier fuel-polymorphic helper
proofs as the primary transport layer. -/

private theorem interpretArgs_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ args types b r,
      r ∈ interpretArgs space dispatch args types b (n + 1) →
      InterpretArgsSync space dispatch (n + 1) args types b r := by
  intro args types b r hr
  match args, types with
  | [], [] =>
      simp only [interpretArgs_succ, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact InterpretArgsSync.nil n b
  | arg :: remArgs, t :: remTypes =>
      simp only [interpretArgs_succ, List.mem_flatMap] at hr
      obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
      by_cases h_cond : (headR != arg && isEmptyOrError headR) = true
      · simp [h_cond] at hr2
        subst hr2
        have h_head : EvalAtomSync space dispatch n arg t b (headR, headB) :=
          ih.evalAtom _ _ _ _ h_head_mem
        have h_changed : headR ≠ arg := by
          cases h1 : (headR != arg) <;> cases h2 : isEmptyOrError headR <;>
            simp_all [bne_iff_ne]
        have h_err : isEmptyOrError headR = true := by
          cases h1 : (headR != arg) <;> cases h2 : isEmptyOrError headR <;> simp_all
        exact InterpretArgsSync.head_changed_error n arg remArgs t remTypes b
          (headR, headB) h_head h_err h_changed
      · have h_cond_false : (headR != arg && isEmptyOrError headR) = false := by
          cases h : (headR != arg && isEmptyOrError headR) <;> simp_all
        simp [h_cond_false] at hr2
        have h_head_ok : isEmptyOrError headR = false ∨ headR = arg := by
          cases he : isEmptyOrError headR with
          | false => exact Or.inl rfl
          | true =>
              right
              by_contra h_ne
              have : (headR != arg) = true := by simp [bne_iff_ne, h_ne]
              simp [this, he] at h_cond
        obtain ⟨tailR, tailB, h_tail_mem, hr3⟩ := hr2
        split at hr3
        · rename_i h_terr
          obtain ⟨rfl, rfl⟩ := hr3
          exact InterpretArgsSync.cons_tail_error n arg remArgs t remTypes b
            (headR, headB) (tailR, tailB)
            (ih.evalAtom _ _ _ _ h_head_mem) h_head_ok
            (ih.interpretArgs _ _ _ _ h_tail_mem) h_terr
        · rename_i h_terr_ne
          have h_terr_false : isEmptyOrError tailR = false := by
            cases h : isEmptyOrError tailR <;> simp_all
          subst hr3
          exact InterpretArgsSync.cons_ok n arg remArgs t remTypes b
            (headR, headB) (tailR, tailB)
            (ih.evalAtom _ _ _ _ h_head_mem) h_head_ok
            (ih.interpretArgs _ _ _ _ h_tail_mem) h_terr_false
  | [], _ :: _ =>
      simp [interpretArgs_succ] at hr
  | _ :: _, [] =>
      simp [interpretArgs_succ] at hr

private theorem interpretTuple_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ atom b r,
      r ∈ interpretTuple space dispatch atom b (n + 1) →
      InterpretTupleSync space dispatch (n + 1) atom b r := by
  intro atom b r hr
  match atom with
  | .expression [single] =>
      exact InterpretTupleSync.singleton n single b r
        (ih.evalAtom single Atom.undefinedType b r (by simpa [interpretTuple_succ] using hr))
  | .expression (hd :: hd2 :: rest) =>
      simp only [interpretTuple_succ, List.mem_flatMap] at hr
      obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
      split at hr2
      · rename_i h_err
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
        subst hr2
        exact InterpretTupleSync.head_error n hd (hd2 :: rest) b
          (headR, headB) (by simp)
          (ih.evalAtom _ _ _ _ h_head_mem) h_err
      · rename_i h_err_ne
        have h_err_false : isEmptyOrError headR = false := by
          cases h : isEmptyOrError headR <;> simp_all
        rw [List.mem_map] at hr2
        obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
        split at hr3
        · rename_i h_terr
          obtain ⟨rfl, rfl⟩ := hr3
          exact InterpretTupleSync.tail_error n hd (hd2 :: rest) b
            (headR, headB) (tailR, tailB) (by simp)
            (ih.evalAtom _ _ _ _ h_head_mem) h_err_false
            (ih.interpretTuple _ _ _ h_tail_mem) h_terr
        · rename_i h_terr_ne
          have h_terr_false : isEmptyOrError tailR = false := by
            cases h : isEmptyOrError tailR <;> simp_all
          obtain ⟨rfl, rfl⟩ := hr3
          exact InterpretTupleSync.success n hd (hd2 :: rest) b
            (headR, headB) (tailR, tailB) (by simp)
            (ih.evalAtom _ _ _ _ h_head_mem) h_err_false
            (ih.interpretTuple _ _ _ h_tail_mem) h_terr_false
  | .expression [] =>
      simp [interpretTuple_succ] at hr
  | .symbol _ =>
      simp [interpretTuple_succ] at hr
  | .var _ =>
      simp [interpretTuple_succ] at hr
  | .grounded _ =>
      simp [interpretTuple_succ] at hr

private theorem interpretFunction_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ atom opType b r,
      r ∈ interpretFunction space dispatch atom opType b (n + 1) →
      InterpretFunctionSync space dispatch (n + 1) atom opType b r := by
  intro atom opType b r hr
  match atom with
  | .expression (op :: args) =>
      simp only [interpretFunction_succ, List.mem_flatMap] at hr
      obtain ⟨⟨headR, headB⟩, h_head_mem, hr2⟩ := hr
      split at hr2
      · rename_i h_err
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
        subst hr2
        exact InterpretFunctionSync.head_error n (.expression (op :: args)) opType b op args
          (headR, headB) rfl
          (ih.evalAtom _ _ _ _ h_head_mem) h_err
      · rename_i h_err_ne
        have h_err_false : isEmptyOrError headR = false := by
          cases h : isEmptyOrError headR <;> simp_all
        match h_argt : getFunctionArgTypes opType with
        | some argTypes =>
            simp only [h_argt] at hr2
            rw [List.mem_map] at hr2
            obtain ⟨⟨tailR, tailB⟩, h_tail_mem, hr3⟩ := hr2
            split at hr3
            · rename_i h_terr
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretFunctionSync.head_ok_tail_error n (.expression (op :: args)) opType b
                op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                (ih.evalAtom _ _ _ _ h_head_mem) h_err_false
                (ih.interpretArgs _ _ _ _ h_tail_mem) h_terr
            · rename_i h_terr_ne
              have h_terr_false : isEmptyOrError tailR = false := by
                cases h : isEmptyOrError tailR <;> simp_all
              obtain ⟨rfl, rfl⟩ := hr3
              exact InterpretFunctionSync.head_ok_tail_ok n (.expression (op :: args)) opType b
                op args argTypes (headR, headB) (tailR, tailB) rfl h_argt
                (ih.evalAtom _ _ _ _ h_head_mem) h_err_false
                (ih.interpretArgs _ _ _ _ h_tail_mem) h_terr_false
        | none =>
            simp only [h_argt, List.not_mem_nil] at hr2
  | .symbol _ =>
      simp [interpretFunction_succ] at hr
  | .var _ =>
      simp [interpretFunction_succ] at hr
  | .grounded _ =>
      simp [interpretFunction_succ] at hr
  | .expression [] =>
      simp [interpretFunction_succ] at hr

private theorem eqMatch_eval_to_sync
    (space : Space) (dispatch : GroundedDispatch) (atom type_ : Atom) (b : Bindings)
    (r : ResultPair) (n : Nat)
    (h_ef : isErrorAtom atom = false)
    (h_ng : match atom with | .expression (op :: _) => dispatch.isExecutable op = false | _ => True)
    (ih_eval : ∀ atom' type_' b' r',
      r' ∈ evalAtom space dispatch atom' type_' b' n →
      EvalAtomSync space dispatch n atom' type_' b' r')
    (hr : r ∈ (if queryEquations space atom n = [] then [(atom, b)]
               else (queryEquations space atom n).flatMap fun x =>
                 (mergeBindings x.2 b n).flatMap fun mb =>
                   if mb.hasLoop = true then []
                   else evalAtom space dispatch (mb.apply x.1 n) type_ mb n)) :
    MettaCallSync space dispatch (n + 1) atom type_ b r := by
  split at hr
  · rename_i h_eqs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact MettaCallSync.no_match n atom type_ b h_ef h_ng h_eqs
  · rename_i h_eqs_ne
    rw [List.mem_flatMap] at hr
    obtain ⟨⟨rhs, qb⟩, h_eq, hr2⟩ := hr
    rw [List.mem_flatMap] at hr2
    obtain ⟨mb, h_merge, hr3⟩ := hr2
    split at hr3
    · rename_i h_loop
      simp at hr3
    · rename_i h_loop_ne
      have h_loop_f : mb.hasLoop = false := by
        cases h : mb.hasLoop <;> simp_all
      exact MettaCallSync.equation_match n atom type_ b rhs qb mb r
        h_ef h_ng h_eq h_merge h_loop_f (ih_eval _ _ _ _ hr3)

private theorem mettaCall_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ atom type_ b r,
      r ∈ mettaCall space dispatch atom type_ b (n + 1) →
      MettaCallSync space dispatch (n + 1) atom type_ b r := by
  intro atom type_ b r hr
  cases h_err : isErrorAtom atom with
  | true =>
      simp [mettaCall, h_err] at hr
      subst r
      exact MettaCallSync.error_passthrough n atom type_ b h_err
  | false =>
      have h_ef : isErrorAtom atom = false := h_err
      match atom with
      | .expression (op :: args) =>
          cases h_exec : dispatch.isExecutable op with
          | true =>
              simp [mettaCall, h_ef, h_exec] at hr
              cases h_run : dispatch.execute op args with
              | ok results =>
                  by_cases h_results : results = []
                  · simp [h_run, h_results] at hr
                    subst r
                    subst results
                    exact MettaCallSync.grounded_empty_results n (.expression (op :: args))
                      type_ b op args rfl h_exec h_ef h_run
                  · simp [h_run, h_results] at hr
                    obtain ⟨nativeR, nativeB, h_nat, mb, h_merge, hr3⟩ := hr
                    exact MettaCallSync.grounded_ok n (.expression (op :: args))
                      type_ b op args results (nativeR, nativeB) mb r
                      rfl h_exec h_ef h_run h_nat h_merge
                      (ih.evalAtom _ _ _ _ hr3)
              | runtimeError msg =>
                  simp [h_run] at hr
                  subst r
                  exact MettaCallSync.grounded_runtime_error n (.expression (op :: args))
                    type_ b op args msg rfl h_exec h_ef h_run
              | noReduce =>
                  simp [h_run] at hr
                  subst r
                  exact MettaCallSync.grounded_no_reduce n (.expression (op :: args))
                    type_ b op args rfl h_exec h_ef h_run
              | incorrectArgument =>
                  simp [h_run] at hr
                  subst r
                  exact MettaCallSync.grounded_incorrect_arg n (.expression (op :: args))
                    type_ b op args rfl h_exec h_ef h_run
          | false =>
              simp [mettaCall, h_ef, h_exec] at hr
              exact eqMatch_eval_to_sync space dispatch _ type_ b r n h_ef
                (by simpa using h_exec) (fun atom' type_' b' r' hr' => ih.evalAtom atom' type_' b' r' hr') hr
      | .symbol _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_eval_to_sync space dispatch _ type_ b r n h_ef
            trivial (fun atom' type_' b' r' hr' => ih.evalAtom atom' type_' b' r' hr') hr
      | .var _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_eval_to_sync space dispatch _ type_ b r n h_ef
            trivial (fun atom' type_' b' r' hr' => ih.evalAtom atom' type_' b' r' hr') hr
      | .grounded _ =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_eval_to_sync space dispatch _ type_ b r n h_ef
            trivial (fun atom' type_' b' r' hr' => ih.evalAtom atom' type_' b' r' hr') hr
      | .expression [] =>
          simp [mettaCall, h_ef] at hr
          exact eqMatch_eval_to_sync space dispatch _ type_ b r n h_ef
            trivial (fun atom' type_' b' r' hr' => ih.evalAtom atom' type_' b' r' hr') hr

private theorem funcResults_to_function_path_sync
    (space : Space) (dispatch : GroundedDispatch)
    (op : Atom) (args : List Atom) (type_ : Atom) (b : Bindings) (r : ResultPair) (n : Nat)
    (ih_func : ∀ atom opType b' r',
      r' ∈ interpretFunction space dispatch atom opType b' n →
      InterpretFunctionSync space dispatch n atom opType b' r')
    (ih_call : ∀ atom' type_' b' r',
      r' ∈ mettaCall space dispatch atom' type_' b' n →
      MettaCallSync space dispatch n atom' type_' b' r')
    (funcType : Atom) (h_ft_mem : funcType ∈ getAtomTypes space op)
    (h_is_func : isFunctionType funcType = true)
    (succs : List Bindings)
    (h_check : checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n = .inr succs)
    (b' : Bindings) (h_b'_mem : b' ∈ succs)
    (interpR : Atom) (interpB : Bindings)
    (h_interp_mem : (interpR, interpB) ∈ interpretFunction space dispatch (.expression (op :: args)) funcType b' n)
    (hr4 : r ∈ mettaCall space dispatch interpR
      (if getFunctionRetType funcType = some Atom.expressionType
       then Atom.undefinedType
       else (getFunctionRetType funcType).getD Atom.undefinedType) interpB n) :
    InterpretExpressionSync space dispatch (n + 1) (.expression (op :: args)) type_ b r :=
  InterpretExpressionSync.function_path n (.expression (op :: args)) type_ b op args funcType b'
    (interpR, interpB) r succs
    rfl h_ft_mem h_is_func h_check h_b'_mem
    (ih_func _ _ _ _ h_interp_mem)
    (by
      simpa [beq_iff_eq] using
        (ih_call _ _ _ _ hr4))

private theorem mem_funcResults_eval_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    (op : Atom) (args : List Atom) (type_ : Atom) (b : Bindings) (r : ResultPair) (n : Nat)
    (ih_func : ∀ atom opType b' r',
      r' ∈ interpretFunction space dispatch atom opType b' n →
      InterpretFunctionSync space dispatch n atom opType b' r')
    (ih_call : ∀ atom' type_' b' r',
      r' ∈ mettaCall space dispatch atom' type_' b' n →
      MettaCallSync space dispatch n atom' type_' b' r')
    (hr : r ∈ (getAtomTypes space op).flatMap fun funcType =>
        if isFunctionType funcType then
          match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
          | .inr succs =>
            succs.flatMap fun b' =>
              (interpretFunction space dispatch (.expression (op :: args)) funcType b' n).flatMap
                fun x => mettaCall space dispatch x.1
                  (if getFunctionRetType funcType = some Atom.expressionType
                   then Atom.undefinedType
                   else (getFunctionRetType funcType).getD Atom.undefinedType) x.2 n
          | .inl _ => []
        else []) :
    InterpretExpressionSync space dispatch (n + 1) (.expression (op :: args)) type_ b r := by
  rw [List.mem_flatMap] at hr
  obtain ⟨funcType, h_ft_mem, hr2⟩ := hr
  split at hr2
  · rename_i h_is_func
    split at hr2
    · rename_i succs h_check
      rw [List.mem_flatMap] at hr2
      obtain ⟨b', h_b'_mem, hr3⟩ := hr2
      rw [List.mem_flatMap] at hr3
      obtain ⟨⟨interpR, interpB⟩, h_interp_mem, hr4⟩ := hr3
      exact funcResults_to_function_path_sync space dispatch op args type_ b r n
        ih_func ih_call funcType h_ft_mem h_is_func succs h_check
        b' h_b'_mem interpR interpB h_interp_mem hr4
    · simp at hr2
  · simp at hr2

private theorem interpretExpression_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ atom type_ b r,
      r ∈ interpretExpression space dispatch atom type_ b (n + 1) →
      InterpretExpressionSync space dispatch (n + 1) atom type_ b r := by
  intro atom type_ b r hr
  simp only [interpretExpression] at hr
  match atom with
  | .expression (op :: args) =>
      simp only [] at hr
      simp only [beq_iff_eq] at hr
      cases h_hasNonFunc : ((getAtomTypes space op).any fun t =>
          !isFunctionType t || t == Atom.undefinedType) with
      | true =>
          simp only [h_hasNonFunc, ite_true] at hr
          split at hr
          · rw [List.mem_append] at hr
            rcases hr with hr_func | hr_tuple
            · exact mem_funcResults_eval_to_sync space dispatch op args type_ b r n
                (fun atom' opType b' r' hr' => ih.interpretFunction atom' opType b' r' hr')
                (fun atom' type_' b' r' hr' => ih.mettaCall atom' type_' b' r' hr')
                hr_func
            · rw [List.mem_flatMap] at hr_tuple
              obtain ⟨⟨tupleR, tupleB⟩, h_tuple_mem, hr3⟩ := hr_tuple
              exact InterpretExpressionSync.tuple_path n (.expression (op :: args)) type_ b
                op args (tupleR, tupleB) r rfl h_hasNonFunc
                (ih.interpretTuple _ _ _ h_tuple_mem)
                (ih.mettaCall _ _ _ _ hr3)
          · simp at hr
      | false =>
          simp [h_hasNonFunc] at hr
          split at hr
          · exact mem_funcResults_eval_to_sync space dispatch op args type_ b r n
              (fun atom' opType b' r' hr' => ih.interpretFunction atom' opType b' r' hr')
              (fun atom' type_' b' r' hr' => ih.mettaCall atom' type_' b' r' hr')
              hr
          · split at hr
            · rename_i h_all_failed
              rw [List.mem_flatMap] at hr
              obtain ⟨funcType, h_ft_mem, hr2⟩ := hr
              split at hr2
              · rename_i h_is_func
                split at hr2
                · rename_i errs h_check
                  rw [List.mem_map] at hr2
                  obtain ⟨e, h_e_mem, h_eq⟩ := hr2
                  subst h_eq
                  have h_all_failed_bool :
                      ((getAtomTypes space op).all fun funcType =>
                        if isFunctionType funcType = true then
                          match checkIfFunctionTypeIsApplicable (.expression (op :: args)) funcType type_ space b n with
                          | .inl _ => true
                          | .inr _ => false
                        else true) = true := by
                    simpa [List.all_eq_true] using h_all_failed
                  exact InterpretExpressionSync.op_type_error n (.expression (op :: args)) type_ b
                    op args funcType errs e rfl h_hasNonFunc h_all_failed_bool
                    h_ft_mem h_is_func h_check h_e_mem
                · simp at hr2
              · simp at hr2
            · simp at hr
  | .expression [] =>
      cases hr
  | .symbol _ =>
      cases hr
  | .var _ =>
      cases hr
  | .grounded _ =>
      cases hr

private theorem evalAtom_eval_to_sync_step
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    ∀ atom type_ b r,
      r ∈ evalAtom space dispatch atom type_ b (n + 1) →
      EvalAtomSync space dispatch (n + 1) atom type_ b r := by
  intro atom type_ b r hr
  cases h_empty : isEmptyOrError atom with
  | true =>
      simp [evalAtom, h_empty] at hr
      subst r
      exact EvalAtomSync.empty_or_error n atom type_ b h_empty
  | false =>
      cases h_tyAtom : type_ == Atom.atomType with
      | true =>
          simp [evalAtom, h_empty, h_tyAtom] at hr
          subst r
          exact EvalAtomSync.type_pass n atom type_ b h_empty
            (Or.inl (beq_iff_eq.mp h_tyAtom))
      | false =>
          cases h_tyMeta : type_ == getMetaType atom with
          | true =>
              simp [evalAtom, h_empty, h_tyAtom, h_tyMeta] at hr
              subst r
              exact EvalAtomSync.type_pass n atom type_ b h_empty
                (Or.inr <| Or.inl (beq_iff_eq.mp h_tyMeta))
          | false =>
              cases h_var : getMetaType atom == Atom.variableType with
              | true =>
                  simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var] at hr
                  subst r
                  exact EvalAtomSync.type_pass n atom type_ b h_empty
                    (Or.inr <| Or.inr (beq_iff_eq.mp h_var))
              | false =>
                  have h_not_pass : ¬(type_ = Atom.atomType
                      ∨ type_ = getMetaType atom
                      ∨ getMetaType atom = Atom.variableType) := by
                    intro h_pass
                    rcases h_pass with h_pass | h_pass | h_pass
                    · simp [h_pass] at h_tyAtom
                    · simp [h_pass] at h_tyMeta
                    · simp [h_pass] at h_var
                  cases h_sym : getMetaType atom == Atom.symbolType with
                  | true =>
                      simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym] at hr
                      exact EvalAtomSync.type_cast n atom type_ b r h_empty h_not_pass
                        (Or.inl (beq_iff_eq.mp h_sym)) hr
                  | false =>
                      cases h_grd : getMetaType atom == Atom.groundedType with
                      | true =>
                          simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd] at hr
                          exact EvalAtomSync.type_cast n atom type_ b r h_empty h_not_pass
                            (Or.inr <| Or.inl (beq_iff_eq.mp h_grd)) hr
                      | false =>
                          cases h_unit : atom == Atom.unit with
                          | true =>
                              simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd, h_unit] at hr
                              exact EvalAtomSync.type_cast n atom type_ b r h_empty h_not_pass
                                (Or.inr <| Or.inr (beq_iff_eq.mp h_unit)) hr
                          | false =>
                              cases h_expr : getMetaType atom == Atom.expressionType with
                              | true =>
                                  have h_expr_eq : getMetaType atom = Atom.expressionType :=
                                    beq_iff_eq.mp h_expr
                                  have h_not_unit : atom ≠ Atom.unit := by
                                    intro h_eq
                                    simp [h_eq] at h_unit
                                  simp [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd, h_unit, h_expr] at hr
                                  by_cases h_succ :
                                      (!(List.filter (fun x => !isErrorAtom x.1)
                                        (interpretExpression space dispatch atom type_ b n)).isEmpty) = true
                                  · simp [h_succ, List.mem_filter] at hr
                                    obtain ⟨h_interp_mem, h_not_err_bool⟩ := hr
                                    have h_not_error : isErrorAtom r.1 = false := by
                                      cases h : isErrorAtom r.1 <;> simp_all
                                    exact EvalAtomSync.interpret_success n atom type_ b r
                                      h_empty h_not_pass h_expr_eq h_not_unit
                                      (ih.interpretExpression _ _ _ _ h_interp_mem) h_not_error
                                  · have h_succ_false :
                                        (!(List.filter (fun x => !isErrorAtom x.1)
                                          (interpretExpression space dispatch atom type_ b n)).isEmpty) = false := by
                                      cases h : (!(List.filter (fun x => !isErrorAtom x.1)
                                        (interpretExpression space dispatch atom type_ b n)).isEmpty) <;> simp_all
                                    simp [h_succ_false, List.mem_filter] at hr
                                    have h_eval_mem :
                                        r ∈ evalAtom space dispatch atom type_ b (n + 1) := by
                                      simpa [evalAtom, h_empty, h_tyAtom, h_tyMeta, h_var, h_sym, h_grd,
                                        h_unit, h_expr, h_succ_false, List.mem_filter] using hr
                                    obtain ⟨h_interp_mem, h_is_error⟩ := hr
                                    have h_all_errors :
                                        OnlyErrorsAt (interpretExpression space dispatch atom type_ b n) := by
                                      intro r' hr_interp
                                      exact (evalAtom_filtered_sound space dispatch atom type_ b n r h_eval_mem).2
                                          h_is_error h_empty r' hr_interp
                                    exact EvalAtomSync.interpret_error n atom type_ b r
                                      h_empty h_not_pass h_expr_eq h_not_unit
                                      (ih.interpretExpression _ _ _ _ h_interp_mem) h_is_error h_all_errors
                              | false =>
                                  cases atom <;> simp [getMetaType] at h_sym h_grd h_var h_expr

private theorem allEvalToSync_succ
    (space : Space) (dispatch : GroundedDispatch) (n : Nat)
    (ih : AllEvalToSync space dispatch n) :
    AllEvalToSync space dispatch (n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact evalAtom_eval_to_sync_step space dispatch n ih
  · exact interpretExpression_eval_to_sync_step space dispatch n ih
  · exact interpretFunction_eval_to_sync_step space dispatch n ih
  · exact interpretArgs_eval_to_sync_step space dispatch n ih
  · exact interpretTuple_eval_to_sync_step space dispatch n ih
  · exact mettaCall_eval_to_sync_step space dispatch n ih

private theorem allEvalToSync
    (space : Space) (dispatch : GroundedDispatch) :
    ∀ fuel, AllEvalToSync space dispatch fuel
  | 0 => allEvalToSync_zero space dispatch
  | n + 1 => allEvalToSync_succ space dispatch n (allEvalToSync space dispatch n)

/-! ### Step 7 exactness corollaries

With both bundled directions in place, the executable kernel and the private
sync model coincide at each fuel. -/

private theorem evalAtom_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    r ∈ evalAtom space dispatch atom type_ b fuel ↔
      EvalAtomSync space dispatch fuel atom type_ b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).evalAtom atom type_ b r
  · exact (allSyncToEval space dispatch fuel).evalAtom atom type_ b r

private theorem interpretExpression_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    r ∈ interpretExpression space dispatch atom type_ b fuel ↔
      InterpretExpressionSync space dispatch fuel atom type_ b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).interpretExpression atom type_ b r
  · exact (allSyncToEval space dispatch fuel).interpretExpression atom type_ b r

private theorem interpretFunction_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom opType : Atom) (b : Bindings) (r : ResultPair) :
    r ∈ interpretFunction space dispatch atom opType b fuel ↔
      InterpretFunctionSync space dispatch fuel atom opType b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).interpretFunction atom opType b r
  · exact (allSyncToEval space dispatch fuel).interpretFunction atom opType b r

private theorem interpretArgs_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (args types : List Atom) (b : Bindings) (r : ResultPair) :
    r ∈ interpretArgs space dispatch args types b fuel ↔
      InterpretArgsSync space dispatch fuel args types b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).interpretArgs args types b r
  · exact (allSyncToEval space dispatch fuel).interpretArgs args types b r

private theorem interpretTuple_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom : Atom) (b : Bindings) (r : ResultPair) :
    r ∈ interpretTuple space dispatch atom b fuel ↔
      InterpretTupleSync space dispatch fuel atom b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).interpretTuple atom b r
  · exact (allSyncToEval space dispatch fuel).interpretTuple atom b r

private theorem mettaCall_exact_at
    (space : Space) (dispatch : GroundedDispatch)
    (fuel : Nat) (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    r ∈ mettaCall space dispatch atom type_ b fuel ↔
      MettaCallSync space dispatch fuel atom type_ b r := by
  constructor
  · exact (allEvalToSync space dispatch fuel).mettaCall atom type_ b r
  · exact (allSyncToEval space dispatch fuel).mettaCall atom type_ b r

/-! ## Public Reachability Soundness

These are the public-facing soundness-half wrappers in the mm-lean4 style:
if the executable evaluator reaches a result at some fuel, then the public
declarative judgment holds. The reverse direction remains the completeness
frontier and is intentionally not claimed here. -/

/-- If `evalAtom` reaches `r` at some fuel, then the public declarative
    `EvalAtom` judgment holds. -/
theorem evalAtom_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ evalAtom space dispatch atom type_ b fuel) →
      EvalAtom space dispatch atom type_ b r := by
  rintro ⟨fuel, hr⟩
  exact evalAtom_sound space dispatch atom type_ b fuel r hr

/-- If `evalAtom` reaches `r` at parent fuel `n + 1`, then the evaluator's
    success-priority filtering is justified at the corresponding subfuel `n`. -/
theorem evalAtom_reaches_filtered_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    (∃ n, r ∈ evalAtom space dispatch atom type_ b (n + 1)) →
      ∃ n, EvalAtomFilteredAtFuel space dispatch atom type_ b n r := by
  rintro ⟨n, hr⟩
  exact ⟨n, evalAtom_filtered_sound space dispatch atom type_ b n r hr⟩

/-- If `interpretExpression` reaches `r` at some fuel, then the public
    declarative `InterpretExpression` judgment holds. -/
theorem interpretExpression_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ interpretExpression space dispatch atom type_ b fuel) →
      InterpretExpression space dispatch atom type_ b r := by
  rintro ⟨fuel, hr⟩
  exact interpretExpression_sound space dispatch atom type_ b fuel r hr

/-- If `interpretFunction` reaches `r` at some fuel, then the public
    declarative `InterpretFunction` judgment holds for every return type. -/
theorem interpretFunction_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ interpretFunction space dispatch atom opType b fuel) →
      ∀ retType, InterpretFunction space dispatch atom opType retType b r := by
  rintro ⟨fuel, hr⟩ retType
  exact interpretFunction_sound space dispatch atom opType b fuel r hr retType

/-- If `interpretArgs` reaches `r` at some fuel, then the public declarative
    `InterpretArgs` judgment holds. -/
theorem interpretArgs_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ interpretArgs space dispatch args types b fuel) →
      InterpretArgs space dispatch args types b r := by
  rintro ⟨fuel, hr⟩
  exact interpretArgs_sound space dispatch args types b fuel r hr

/-- If `interpretTuple` reaches `r` at some fuel, then the public declarative
    `InterpretTuple` judgment holds. -/
theorem interpretTuple_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ interpretTuple space dispatch atom b fuel) →
      InterpretTuple space dispatch atom b r := by
  rintro ⟨fuel, hr⟩
  exact interpretTuple_sound space dispatch atom b fuel r hr

/-- If `mettaCall` reaches `r` at some fuel, then the public declarative
    `MettaCall` judgment holds. -/
theorem mettaCall_reaches_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    (∃ fuel, r ∈ mettaCall space dispatch atom type_ b fuel) →
      MettaCall space dispatch atom type_ b r := by
  rintro ⟨fuel, hr⟩
  exact mettaCall_sound space dispatch atom type_ b fuel r hr

/-! ## Public aligned completeness witnesses

The public declarative HE spec is intentionally coarser than the executable
mirror. The audit above isolates two places where a direct `EvalSpec → Sync`
translation is too optimistic:

- `EvalAtom.interpret_error` needs a negative "all public expression derivations
  are errors" premise before it can justify the sync model's local
  `OnlyErrorsAt ...` condition.
- `MettaCall.empty_results` has no exact executable counterpart and therefore
  must be excluded from the aligned completeness bridge.

The following proof-only relations strengthen exactly those sites and otherwise
mirror the public declarative structure. They are not a second public spec; they
are the intermediate bridge promised in the manifesto. -/

private def TypeCastEventually (space : Space) (atom type_ : Atom)
    (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 → r ∈ typeCast atom type_ space b fuel

private def QueryEquationEventually (space : Space) (atom rhs : Atom)
    (queryBindings : Bindings) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 → (rhs, queryBindings) ∈ queryEquations space atom fuel

private def QueryNoMatchEventually (space : Space) (atom : Atom) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 → queryEquations space atom fuel = []

private def MergeBindingsEventually (left right merged : Bindings) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 → merged ∈ mergeBindings left right fuel

private def ApplyStableEventually (b : Bindings) (rhs applied : Atom) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 → b.apply rhs fuel = applied

private def CheckApplicableMemberEventually
    (space : Space) (expr funcType expectedType : Atom) (b b' : Bindings) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    ∃ succs,
      checkIfFunctionTypeIsApplicable expr funcType expectedType space b fuel = .inr succs
      ∧ b' ∈ succs

private def CheckApplicableErrorEventually
    (space : Space) (expr funcType expectedType : Atom) (b : Bindings)
    (errAtom : Atom) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    ∃ errs,
      checkIfFunctionTypeIsApplicable expr funcType expectedType space b fuel = .inl errs
      ∧ errAtom ∈ errs

private def CheckApplicableAllFailEventually
    (space : Space) (atom op type_ : Atom) (b : Bindings) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    ∀ ft ∈ getAtomTypes space op,
      isFunctionType ft = true →
      ∃ errs, checkIfFunctionTypeIsApplicable atom ft type_ space b fuel = .inl errs

mutual

private inductive EvalAtomAligned (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  | empty_or_error (atom type_ : Atom) (b : Bindings)
      (h : isEmptyOrError atom = true) :
      EvalAtomAligned space dispatch atom type_ b (atom, b)
  | type_pass (atom type_ : Atom) (b : Bindings)
      (h_not_empty : isEmptyOrError atom = false)
      (h_pass : type_ = Atom.atomType
              ∨ type_ = getMetaType atom
              ∨ getMetaType atom = Atom.variableType) :
      EvalAtomAligned space dispatch atom type_ b (atom, b)
  | type_cast (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_cast_branch : getMetaType atom = Atom.symbolType
                     ∨ getMetaType atom = Atom.groundedType
                     ∨ atom = Atom.unit)
      (h_result_eventual : TypeCastEventually space atom type_ b r) :
      EvalAtomAligned space dispatch atom type_ b r
  | interpret_success (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpressionAligned space dispatch atom type_ b r)
      (h_not_error : isErrorAtom r.1 = false) :
      EvalAtomAligned space dispatch atom type_ b r
  | interpret_error (atom type_ : Atom) (b : Bindings) (r : ResultPair)
      (h_not_empty : isEmptyOrError atom = false)
      (h_not_pass : ¬(type_ = Atom.atomType
                     ∨ type_ = getMetaType atom
                     ∨ getMetaType atom = Atom.variableType))
      (h_expr : getMetaType atom = Atom.expressionType)
      (h_not_unit : atom ≠ Atom.unit)
      (h_interp : InterpretExpressionAligned space dispatch atom type_ b r)
      (h_is_error : isErrorAtom r.1 = true)
      (h_all_errors : ∀ r' : ResultPair,
        InterpretExpression space dispatch atom type_ b r' →
        isErrorAtom r'.1 = true) :
      EvalAtomAligned space dispatch atom type_ b r

private inductive InterpretExpressionAligned (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  | function_path (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (funcType retType : Atom) (b' : Bindings)
      (interpResult callResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_op_type : funcType ∈ getAtomTypes space op)
      (h_is_func : isFunctionType funcType = true)
      (h_check_eventual :
        CheckApplicableMemberEventually space atom funcType type_ b b')
      (h_ret : retType = (if getFunctionRetType funcType = some Atom.expressionType
                           then Atom.undefinedType
                           else (getFunctionRetType funcType).getD Atom.undefinedType))
      (h_interp : InterpretFunctionAligned space dispatch atom funcType retType b' interpResult)
      (h_call : MettaCallAligned space dispatch interpResult.1 retType interpResult.2 callResult) :
      InterpretExpressionAligned space dispatch atom type_ b callResult
  | tuple_path (atom type_ : Atom) (b : Bindings)
      (tupleResult callResult : ResultPair)
      (h_has_non_func : ∃ t ∈ getAtomTypes space (match atom with
                          | .expression (op :: _) => op | _ => atom),
                        isFunctionType t = false ∨ t = Atom.undefinedType)
      (h_tuple : InterpretTupleAligned space dispatch atom b tupleResult)
      (h_call : MettaCallAligned space dispatch tupleResult.1 type_ tupleResult.2 callResult) :
      InterpretExpressionAligned space dispatch atom type_ b callResult
  | op_type_error (atom type_ : Atom) (b : Bindings) (op : Atom) (args : List Atom)
      (errAtom failedType : Atom)
      (h_shape : atom = .expression (op :: args))
      (h_all_fail_eventual :
        CheckApplicableAllFailEventually space atom op type_ b)
      (h_no_non_func : ∀ t ∈ getAtomTypes space op,
        isFunctionType t = true ∧ t ≠ Atom.undefinedType)
      (h_failed_type : failedType ∈ getAtomTypes space op)
      (h_failed_func : isFunctionType failedType = true)
      (h_check_fail_eventual :
        CheckApplicableErrorEventually space atom failedType type_ b errAtom) :
      InterpretExpressionAligned space dispatch atom type_ b (errAtom, b)

private inductive InterpretFunctionAligned (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Atom → Bindings → ResultPair → Prop where
  | head_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (headResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_head : EvalAtomAligned space dispatch op opType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretFunctionAligned space dispatch atom opType retType b headResult
  | head_ok_tail_error (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtomAligned space dispatch op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgsAligned space dispatch args argTypes headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretFunctionAligned space dispatch atom opType retType b tailResult
  | head_ok_tail_ok (atom opType retType : Atom) (b : Bindings)
      (op : Atom) (args argTypes : List Atom) (headResult tailResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_arg_types : getFunctionArgTypes opType = some argTypes)
      (h_head : EvalAtomAligned space dispatch op opType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretArgsAligned space dispatch args argTypes headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretFunctionAligned space dispatch atom opType retType b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

private inductive InterpretArgsAligned (space : Space) (dispatch : GroundedDispatch) :
    List Atom → List Atom → Bindings → ResultPair → Prop where
  | nil (b : Bindings) :
      InterpretArgsAligned space dispatch [] [] b (Atom.unit, b)
  | head_changed_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult : ResultPair)
      (h_head : EvalAtomAligned space dispatch a t b headResult)
      (h_err : isEmptyOrError headResult.1 = true)
      (h_changed : headResult.1 ≠ a) :
      InterpretArgsAligned space dispatch (a :: as) (t :: ts) b headResult
  | cons_tail_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtomAligned space dispatch a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgsAligned space dispatch as ts headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretArgsAligned space dispatch (a :: as) (t :: ts) b tailResult
  | cons_ok (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : EvalAtomAligned space dispatch a t b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : InterpretArgsAligned space dispatch as ts headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretArgsAligned space dispatch (a :: as) (t :: ts) b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

private inductive InterpretTupleAligned (space : Space) (dispatch : GroundedDispatch) :
    Atom → Bindings → ResultPair → Prop where
  | singleton (a : Atom) (b : Bindings) (r : ResultPair)
      (h_eval : EvalAtomAligned space dispatch a Atom.undefinedType b r) :
      InterpretTupleAligned space dispatch (.expression [a]) b r
  | head_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomAligned space dispatch hd Atom.undefinedType b headResult)
      (h_err : isEmptyOrError headResult.1 = true) :
      InterpretTupleAligned space dispatch (.expression (hd :: tl)) b headResult
  | tail_error (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomAligned space dispatch hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTupleAligned space dispatch (.expression tl) headResult.2 tailResult)
      (h_tail_err : isEmptyOrError tailResult.1 = true) :
      InterpretTupleAligned space dispatch (.expression (hd :: tl)) b tailResult
  | success (hd : Atom) (tl : List Atom) (b : Bindings)
      (headResult tailResult : ResultPair)
      (h_tl_nonempty : tl ≠ [])
      (h_head : EvalAtomAligned space dispatch hd Atom.undefinedType b headResult)
      (h_head_ok : isEmptyOrError headResult.1 = false)
      (h_tail : InterpretTupleAligned space dispatch (.expression tl) headResult.2 tailResult)
      (h_tail_ok : isEmptyOrError tailResult.1 = false) :
      InterpretTupleAligned space dispatch (.expression (hd :: tl)) b
        (.expression (headResult.1 :: atomElements tailResult.1), tailResult.2)

private inductive MettaCallAligned (space : Space) (dispatch : GroundedDispatch) :
    Atom → Atom → Bindings → ResultPair → Prop where
  | error_passthrough (atom type_ : Atom) (b : Bindings)
      (h_err : isErrorAtom atom = true) :
      MettaCallAligned space dispatch atom type_ b (atom, b)
  | grounded_ok (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (nativeResults : ResultSet) (nativeResult : ResultPair)
      (merged : Bindings) (finalResult : ResultPair)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok nativeResults)
      (h_native_mem : nativeResult ∈ nativeResults)
      (h_merge_eventual :
        MergeBindingsEventually nativeResult.2 b merged)
      (h_recurse : EvalAtomAligned space dispatch nativeResult.1 type_ merged finalResult) :
      MettaCallAligned space dispatch atom type_ b finalResult
  | grounded_runtime_error (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom) (msg : String)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .runtimeError msg) :
      MettaCallAligned space dispatch atom type_ b
        (Atom.error atom (.symbol msg), b)
  | grounded_no_reduce (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .noReduce) :
      MettaCallAligned space dispatch atom type_ b (atom, b)
  | grounded_incorrect_arg (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .incorrectArgument) :
      MettaCallAligned space dispatch atom type_ b (atom, b)
  | grounded_empty_results (atom type_ : Atom) (b : Bindings)
      (op : Atom) (args : List Atom)
      (h_shape : atom = .expression (op :: args))
      (h_exec : dispatch.isExecutable op = true)
      (h_not_error : isErrorAtom atom = false)
      (h_native : dispatch.execute op args = .ok []) :
      MettaCallAligned space dispatch atom type_ b (Atom.empty, b)
  | equation_match (atom type_ : Atom) (b : Bindings)
      (rhs applied : Atom) (queryBindings merged : Bindings)
      (finalResult : ResultPair)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_query_eventual :
        QueryEquationEventually space atom rhs queryBindings)
      (h_merge_eventual :
        MergeBindingsEventually queryBindings b merged)
      (h_no_loop : merged.hasLoop = false)
      (h_apply_stable :
        ApplyStableEventually merged rhs applied)
      (h_recurse : EvalAtomAligned space dispatch applied type_ merged finalResult) :
      MettaCallAligned space dispatch atom type_ b finalResult
  | no_match (atom type_ : Atom) (b : Bindings)
      (h_not_error : isErrorAtom atom = false)
      (h_not_grounded : match atom with
        | .expression (op :: _) => dispatch.isExecutable op = false
        | _ => True)
      (h_no_eqs_eventual : QueryNoMatchEventually space atom) :
      MettaCallAligned space dispatch atom type_ b (atom, b)

end

/-! ### Prototype completeness leg: aligned `EvalAtom`

This is the first public-completeness prototype above the exact sync bridge.
It shows the intended transport shape for the top-level evaluator: once the
aligned `InterpretExpression` completeness leg exists, the strengthened public
`EvalAtom` witness maps to some synchronous fuel immediately. -/

private theorem evalAtomAligned_to_sync_of_interpretExpression_complete
    (space : Space) (dispatch : GroundedDispatch)
    (h_interp_complete : ∀ atom type_ b r,
      InterpretExpressionAligned space dispatch atom type_ b r →
      ∃ fuel, InterpretExpressionSync space dispatch fuel atom type_ b r) :
    ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel, EvalAtomSync space dispatch fuel atom type_ b r := by
  intro atom type_ b r h
  cases h with
  | empty_or_error atom type_ b h_empty =>
      exact ⟨1, by simpa using (EvalAtomSync.empty_or_error 0 atom type_ b h_empty)⟩
  | type_pass atom type_ b h_not_empty h_pass =>
      exact ⟨1, by simpa using (EvalAtomSync.type_pass 0 atom type_ b h_not_empty h_pass)⟩
  | type_cast atom type_ b r h_not_empty h_not_pass h_cast_branch h_result_eventual =>
      obtain ⟨fuel0, h_result_eventual⟩ := h_result_eventual
      exact ⟨fuel0 + 1, by
        simpa using
          (EvalAtomSync.type_cast fuel0 atom type_ b r
            h_not_empty h_not_pass h_cast_branch
            (h_result_eventual fuel0 (le_rfl)))⟩
  | interpret_success atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_not_error =>
      obtain ⟨fuel, h_interp_sync⟩ := h_interp_complete atom type_ b r h_interp
      cases fuel with
      | zero =>
          exfalso
          exact not_interpretExpressionSync_zero space dispatch atom type_ b r h_interp_sync
      | succ n =>
          exact ⟨n + 2,
            EvalAtomSync.interpret_success (n + 1) atom type_ b r
              h_not_empty h_not_pass h_expr h_not_unit h_interp_sync h_not_error⟩
  | interpret_error atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_is_error h_all_errors =>
      obtain ⟨fuel, h_interp_sync⟩ := h_interp_complete atom type_ b r h_interp
      cases fuel with
      | zero =>
          exfalso
          exact not_interpretExpressionSync_zero space dispatch atom type_ b r h_interp_sync
      | succ n =>
          have h_only_errors :
              OnlyErrorsAt (interpretExpression space dispatch atom type_ b (n + 1)) := by
            intro r' hr'
            exact h_all_errors r'
              (interpretExpression_sound space dispatch atom type_ b (n + 1) r' hr')
          exact ⟨n + 2,
            EvalAtomSync.interpret_error (n + 1) atom type_ b r
              h_not_empty h_not_pass h_expr h_not_unit h_interp_sync h_is_error h_only_errors⟩

/-! ### Prototype public completeness: `EvalAtomFiltered`

This is the first public-facing completeness theorem on the honest HE-compatible
surface. It does not claim full 6-way completeness yet; instead it isolates the
top-level `evalAtom` leg and shows that once `InterpretExpression` has the same
public reachability completeness, the filtered public `EvalAtom` judgment does
too. -/

theorem evalAtomFiltered_reaches_complete_of_interpretExpression_complete
    (space : Space) (dispatch : GroundedDispatch)
    (h_interp_complete : ∀ atom type_ b r,
      InterpretExpression space dispatch atom type_ b r →
      ∃ fuel, r ∈ interpretExpression space dispatch atom type_ b fuel) :
    ∀ atom type_ b r,
      EvalAtomFiltered space dispatch atom type_ b r →
      ∃ fuel, r ∈ evalAtom space dispatch atom type_ b fuel := by
  intro atom type_ b r h_filtered
  rcases h_filtered with ⟨h_eval, h_all_errors⟩
  cases h_eval with
  | empty_or_error atom type_ b h_empty =>
      refine ⟨1, ?_⟩
      simpa using
        ((evalAtom_exact_at space dispatch 1 atom type_ b (atom, b)).mpr
          (EvalAtomSync.empty_or_error 0 atom type_ b h_empty))
  | type_pass atom type_ b h_not_empty h_pass =>
      refine ⟨1, ?_⟩
      simpa using
        ((evalAtom_exact_at space dispatch 1 atom type_ b (atom, b)).mpr
          (EvalAtomSync.type_pass 0 atom type_ b h_not_empty h_pass))
  | type_cast atom type_ b r fuel h_not_empty h_not_pass h_cast_branch h_result =>
      refine ⟨fuel + 1, ?_⟩
      simpa using
        ((evalAtom_exact_at space dispatch (fuel + 1) atom type_ b r).mpr
          (EvalAtomSync.type_cast fuel atom type_ b r
            h_not_empty h_not_pass h_cast_branch h_result))
  | interpret_success atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_not_error =>
      obtain ⟨fuel, hr_interp⟩ := h_interp_complete atom type_ b r h_interp
      have h_interp_sync :
          InterpretExpressionSync space dispatch fuel atom type_ b r :=
        (interpretExpression_exact_at space dispatch fuel atom type_ b r).mp hr_interp
      cases fuel with
      | zero =>
          exfalso
          exact not_interpretExpressionSync_zero space dispatch atom type_ b r h_interp_sync
      | succ n =>
          refine ⟨n + 2, ?_⟩
          simpa using
            ((evalAtom_exact_at space dispatch (n + 2) atom type_ b r).mpr
              (EvalAtomSync.interpret_success (n + 1) atom type_ b r
                h_not_empty h_not_pass h_expr h_not_unit h_interp_sync h_not_error))
  | interpret_error atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_is_error =>
      obtain ⟨fuel, hr_interp⟩ := h_interp_complete atom type_ b r h_interp
      have h_interp_sync :
          InterpretExpressionSync space dispatch fuel atom type_ b r :=
        (interpretExpression_exact_at space dispatch fuel atom type_ b r).mp hr_interp
      cases fuel with
      | zero =>
          exfalso
          exact not_interpretExpressionSync_zero space dispatch atom type_ b r h_interp_sync
      | succ n =>
          have h_only_errors :
              OnlyErrorsAt (interpretExpression space dispatch atom type_ b (n + 1)) := by
            intro r' hr'
            exact h_all_errors h_is_error r'
              (interpretExpression_sound space dispatch atom type_ b (n + 1) r' hr')
          refine ⟨n + 2, ?_⟩
          simpa using
            ((evalAtom_exact_at space dispatch (n + 2) atom type_ b r).mpr
              (EvalAtomSync.interpret_error (n + 1) atom type_ b r
                h_not_empty h_not_pass h_expr h_not_unit h_interp_sync h_is_error h_only_errors))

/-! ### Eventual aligned reachability for the simple trio

These lemmas are the council-approved replacement for the earlier failed
monotonicity detour. Instead of proving that evaluator results persist by a
global monotonicity theorem, we prove a stronger completeness shape directly:
once an aligned derivation becomes reachable, it remains reachable at every
larger fuel. This gives sibling subcalls a common subfuel by construction. -/

private theorem interpretArgsAligned_eventually_to_sync_of_evalAtom_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval_eventual : ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ args types b r,
      InterpretArgsAligned space dispatch args types b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretArgsSync space dispatch fuel args types b r := by
  let rec go {args types : List Atom} {b : Bindings} {r : ResultPair}
      (h : InterpretArgsAligned space dispatch args types b r) :
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretArgsSync space dispatch fuel args types b r := by
    match h with
    | .nil b =>
        refine ⟨1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            simpa using (InterpretArgsSync.nil (space := space) (dispatch := dispatch) n b)
    | .head_changed_error a as t ts b headResult h_head h_err h_changed =>
        obtain ⟨fuel0, h_head_eventual⟩ := h_eval_eventual a t b headResult h_head
        refine ⟨fuel0 + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            have hn : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
            exact InterpretArgsSync.head_changed_error n a as t ts b headResult
              (h_head_eventual n hn) h_err h_changed
    | .cons_tail_error a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_err =>
        obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual a t b headResult h_head
        obtain ⟨fuelTail, h_tail_eventual⟩ := go h_tail
        refine ⟨max fuelHead fuelTail + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
            have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
            have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
            exact InterpretArgsSync.cons_tail_error n a as t ts b headResult tailResult
              (h_head_eventual n hn_head) h_head_ok
              (h_tail_eventual n hn_tail) h_tail_err
    | .cons_ok a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_ok =>
        obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual a t b headResult h_head
        obtain ⟨fuelTail, h_tail_eventual⟩ := go h_tail
        refine ⟨max fuelHead fuelTail + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
            have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
            have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
            exact InterpretArgsSync.cons_ok n a as t ts b headResult tailResult
              (h_head_eventual n hn_head) h_head_ok
              (h_tail_eventual n hn_tail) h_tail_ok
  intro args types b r h
  exact go h

private theorem interpretTupleAligned_eventually_to_sync_of_evalAtom_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval_eventual : ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ atom b r,
      InterpretTupleAligned space dispatch atom b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretTupleSync space dispatch fuel atom b r := by
  let rec go {atom : Atom} {b : Bindings} {r : ResultPair}
      (h : InterpretTupleAligned space dispatch atom b r) :
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretTupleSync space dispatch fuel atom b r := by
    match h with
    | .singleton a b r h_eval =>
        obtain ⟨fuel0, h_eval_eventual⟩ := h_eval_eventual a Atom.undefinedType b r h_eval
        refine ⟨fuel0 + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            exact InterpretTupleSync.singleton n a b r (h_eval_eventual n (Nat.succ_le_succ_iff.mp hfuel))
    | .head_error hd tl b headResult h_tl_nonempty h_head h_err =>
        obtain ⟨fuel0, h_head_eventual⟩ := h_eval_eventual hd Atom.undefinedType b headResult h_head
        refine ⟨fuel0 + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            exact InterpretTupleSync.head_error n hd tl b headResult
              h_tl_nonempty (h_head_eventual n (Nat.succ_le_succ_iff.mp hfuel)) h_err
    | .tail_error hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
        obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual hd Atom.undefinedType b headResult h_head
        obtain ⟨fuelTail, h_tail_eventual⟩ := go h_tail
        refine ⟨max fuelHead fuelTail + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
            have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
            have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
            exact InterpretTupleSync.tail_error n hd tl b headResult tailResult
              h_tl_nonempty (h_head_eventual n hn_head) h_head_ok
              (h_tail_eventual n hn_tail) h_tail_err
    | .success hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
        obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual hd Atom.undefinedType b headResult h_head
        obtain ⟨fuelTail, h_tail_eventual⟩ := go h_tail
        refine ⟨max fuelHead fuelTail + 1, ?_⟩
        intro fuel hfuel
        cases fuel with
        | zero => cases hfuel
        | succ n =>
            have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
            have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
            have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
            exact InterpretTupleSync.success n hd tl b headResult tailResult
              h_tl_nonempty (h_head_eventual n hn_head) h_head_ok
              (h_tail_eventual n hn_tail) h_tail_ok
  intro atom b r h
  exact go h

private theorem interpretFunctionAligned_eventually_to_sync_of_evalAtom_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval_eventual : ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ atom opType retType b r,
      InterpretFunctionAligned space dispatch atom opType retType b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretFunctionSync space dispatch fuel atom opType b r := by
  intro atom opType retType b r h
  have h_args_eventual := interpretArgsAligned_eventually_to_sync_of_evalAtom_eventually
    space dispatch h_eval_eventual
  match h with
  | .head_error atom opType retType b op args headResult h_shape h_head h_err =>
      obtain ⟨fuel0, h_head_eventual⟩ := h_eval_eventual op opType b headResult h_head
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact InterpretFunctionSync.head_error n atom opType b op args headResult
            h_shape (h_head_eventual n (Nat.succ_le_succ_iff.mp hfuel)) h_err
  | .head_ok_tail_error atom opType retType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_err =>
      obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual op opType b headResult h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ := h_args_eventual args argTypes headResult.2 tailResult h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretFunctionSync.head_ok_tail_error n atom opType b op args argTypes
            headResult tailResult h_shape h_arg_types
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_err
  | .head_ok_tail_ok atom opType retType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_ok =>
      obtain ⟨fuelHead, h_head_eventual⟩ := h_eval_eventual op opType b headResult h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ := h_args_eventual args argTypes headResult.2 tailResult h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretFunctionSync.head_ok_tail_ok n atom opType b op args argTypes
            headResult tailResult h_shape h_arg_types
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_ok

private theorem mettaCallAligned_eventually_to_sync_of_evalAtom_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval_eventual : ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ atom type_ b r,
      MettaCallAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        MettaCallSync space dispatch fuel atom type_ b r := by
  intro atom type_ b r h
  match h with
  | .error_passthrough atom type_ b h_err =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (MettaCallSync.error_passthrough n atom type_ b h_err)
  | .grounded_ok atom type_ b op args nativeResults nativeResult merged finalResult
      h_shape h_exec h_not_error h_native h_native_mem h_merge_eventual h_recurse =>
      obtain ⟨fuelMerge, h_merge_eventual⟩ := h_merge_eventual
      obtain ⟨fuelEval, h_eval_eventual⟩ := h_eval_eventual nativeResult.1 type_ merged finalResult h_recurse
      refine ⟨max fuelMerge fuelEval + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelMerge fuelEval := Nat.succ_le_succ_iff.mp hfuel
          have hn_merge : n ≥ fuelMerge := le_trans (Nat.le_max_left fuelMerge fuelEval) hn_max
          have hn_eval : n ≥ fuelEval := le_trans (Nat.le_max_right fuelMerge fuelEval) hn_max
          exact MettaCallSync.grounded_ok n atom type_ b op args nativeResults nativeResult
            merged finalResult h_shape h_exec h_not_error h_native h_native_mem
            (h_merge_eventual n hn_merge) (h_eval_eventual n hn_eval)
  | .grounded_runtime_error atom type_ b op args msg h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_runtime_error n atom type_ b op args msg
              h_shape h_exec h_not_error h_native)
  | .grounded_no_reduce atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_no_reduce n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .grounded_incorrect_arg atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_incorrect_arg n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .grounded_empty_results atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_empty_results n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .equation_match atom type_ b rhs applied queryBindings merged finalResult
      h_not_error h_not_grounded h_query_eventual h_merge_eventual h_no_loop
      h_apply_stable h_recurse =>
      obtain ⟨fuelQuery, h_query_eventual⟩ := h_query_eventual
      obtain ⟨fuelMerge, h_merge_eventual⟩ := h_merge_eventual
      obtain ⟨fuelApply, h_apply_stable⟩ := h_apply_stable
      obtain ⟨fuelEval, h_eval_eventual⟩ := h_eval_eventual applied type_ merged finalResult h_recurse
      let fuel0 := max (max fuelQuery fuelMerge) (max fuelApply fuelEval)
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_fuel0 : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
          have hn_query : n ≥ fuelQuery := by
            exact le_trans (Nat.le_max_left fuelQuery fuelMerge) <|
              le_trans (Nat.le_max_left (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_merge : n ≥ fuelMerge := by
            exact le_trans (Nat.le_max_right fuelQuery fuelMerge) <|
              le_trans (Nat.le_max_left (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_apply : n ≥ fuelApply := by
            exact le_trans (Nat.le_max_left fuelApply fuelEval) <|
              le_trans (Nat.le_max_right (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_eval : n ≥ fuelEval := by
            exact le_trans (Nat.le_max_right fuelApply fuelEval) <|
              le_trans (Nat.le_max_right (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have h_apply_eq : merged.apply rhs n = applied := h_apply_stable n hn_apply
          exact MettaCallSync.equation_match n atom type_ b rhs queryBindings merged finalResult
            h_not_error h_not_grounded
            (h_query_eventual n hn_query)
            (h_merge_eventual n hn_merge)
            h_no_loop
            (by simpa [h_apply_eq] using h_eval_eventual n hn_eval)
  | .no_match atom type_ b h_not_error h_not_grounded h_no_eqs_eventual =>
      obtain ⟨fuel0, h_no_eqs_eventual⟩ := h_no_eqs_eventual
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact MettaCallSync.no_match n atom type_ b h_not_error h_not_grounded
            (h_no_eqs_eventual n (Nat.succ_le_succ_iff.mp hfuel))

private theorem interpretExpressionAligned_eventually_to_sync_of_evalAtom_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_eval_eventual : ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r) :
    ∀ atom type_ b r,
      InterpretExpressionAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretExpressionSync space dispatch fuel atom type_ b r := by
  intro atom type_ b r h
  have h_func_eventual := interpretFunctionAligned_eventually_to_sync_of_evalAtom_eventually
    space dispatch h_eval_eventual
  have h_tuple_eventual := interpretTupleAligned_eventually_to_sync_of_evalAtom_eventually
    space dispatch h_eval_eventual
  have h_call_eventual := mettaCallAligned_eventually_to_sync_of_evalAtom_eventually
    space dispatch h_eval_eventual
  match h with
  | .function_path atom type_ b op args funcType retType b' interpResult callResult
      h_shape h_op_type h_is_func h_check_eventual h_ret h_interp h_call =>
      obtain ⟨fuelCheck, h_check_eventual⟩ := h_check_eventual
      obtain ⟨fuelInterp, h_interp_eventual⟩ := h_func_eventual atom funcType retType b' interpResult h_interp
      obtain ⟨fuelCall, h_call_eventual⟩ := h_call_eventual interpResult.1 retType interpResult.2 callResult h_call
      let fuel0 := max fuelCheck (max fuelInterp fuelCall)
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_fuel0 : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
          have hn_check : n ≥ fuelCheck := by
            exact le_trans (Nat.le_max_left fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          have hn_interp : n ≥ fuelInterp := by
            exact le_trans (Nat.le_max_left fuelInterp fuelCall) <|
              le_trans (Nat.le_max_right fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          have hn_call : n ≥ fuelCall := by
            exact le_trans (Nat.le_max_right fuelInterp fuelCall) <|
              le_trans (Nat.le_max_right fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          obtain ⟨succs, h_check, h_check_b⟩ := h_check_eventual n hn_check
          exact InterpretExpressionSync.function_path n atom type_ b op args funcType b'
            interpResult callResult succs h_shape h_op_type h_is_func h_check h_check_b
            (h_interp_eventual n hn_interp)
            (by simpa [h_ret, beq_iff_eq] using h_call_eventual n hn_call)
  | .tuple_path atom type_ b tupleResult callResult h_has_non_func h_tuple h_call =>
      obtain ⟨fuelTuple, h_tuple_eventual⟩ := h_tuple_eventual atom b tupleResult h_tuple
      obtain ⟨fuelCall, h_call_eventual⟩ := h_call_eventual tupleResult.1 type_ tupleResult.2 callResult h_call
      have h_shape_ex : ∃ op args, atom = .expression (op :: args) := by
        cases h_tuple with
        | singleton a b r h_eval =>
            exact ⟨a, [], rfl⟩
        | head_error hd tl b headResult h_tl_nonempty h_head h_err =>
            exact ⟨hd, tl, rfl⟩
        | tail_error hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
            exact ⟨hd, tl, rfl⟩
        | success hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
            exact ⟨hd, tl, rfl⟩
      obtain ⟨op, args, h_shape⟩ := h_shape_ex
      have h_has_non_func_bool :
          ((getAtomTypes space op).any fun t =>
            !isFunctionType t || t == Atom.undefinedType) = true := by
        simpa [h_shape, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] using h_has_non_func
      refine ⟨max fuelTuple fuelCall + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelTuple fuelCall := Nat.succ_le_succ_iff.mp hfuel
          have hn_tuple : n ≥ fuelTuple := le_trans (Nat.le_max_left fuelTuple fuelCall) hn_max
          have hn_call : n ≥ fuelCall := le_trans (Nat.le_max_right fuelTuple fuelCall) hn_max
          exact InterpretExpressionSync.tuple_path n atom type_ b op args tupleResult callResult
            h_shape h_has_non_func_bool
            (h_tuple_eventual n hn_tuple)
            (h_call_eventual n hn_call)
  | .op_type_error atom type_ b op args errAtom failedType h_shape
      h_all_fail_eventual h_no_non_func h_failed_type h_failed_func h_check_fail_eventual =>
      obtain ⟨fuelAll, h_all_fail_eventual⟩ := h_all_fail_eventual
      obtain ⟨fuelFail, h_check_fail_eventual⟩ := h_check_fail_eventual
      refine ⟨max fuelAll fuelFail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelAll fuelFail := Nat.succ_le_succ_iff.mp hfuel
          have hn_all : n ≥ fuelAll := le_trans (Nat.le_max_left fuelAll fuelFail) hn_max
          have hn_fail : n ≥ fuelFail := le_trans (Nat.le_max_right fuelAll fuelFail) hn_max
          obtain ⟨errs, h_check_fail, h_err_mem⟩ := h_check_fail_eventual n hn_fail
          have h_has_non_func_false :
              ((getAtomTypes space op).any fun t =>
                !isFunctionType t || t == Atom.undefinedType) = false := by
            by_cases h_any :
                ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) = true
            · have h_exists :
                  ∃ t ∈ getAtomTypes space op,
                    isFunctionType t = false ∨ t = Atom.undefinedType := by
                simpa [List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] using h_any
              rcases h_exists with ⟨t, h_t_mem, h_bad⟩
              rcases h_no_non_func t h_t_mem with ⟨h_t_func, h_t_not_undef⟩
              cases h_bad with
              | inl h_not_func =>
                  have : False := by
                    simp [h_t_func] at h_not_func
                  exact this.elim
              | inr h_undef =>
                  exact (h_t_not_undef h_undef).elim
            · cases h_bool :
                  ((getAtomTypes space op).any fun t =>
                    !isFunctionType t || t == Atom.undefinedType) <;> simp_all
          have h_all_fail_bool :
              ((getAtomTypes space op).all fun funcType =>
                if isFunctionType funcType then
                  match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
                  | .inl _ => true
                  | .inr _ => false
                else true) = true := by
            rw [List.all_eq_true]
            intro ft h_ft_mem
            by_cases h_is_func : isFunctionType ft = true
            · obtain ⟨errs', h_fail⟩ := h_all_fail_eventual n hn_all ft h_ft_mem h_is_func
              simp [h_is_func, h_fail]
            · simp [h_is_func]
          exact InterpretExpressionSync.op_type_error n atom type_ b op args failedType errs errAtom
            h_shape h_has_non_func_false h_all_fail_bool
            h_failed_type h_failed_func h_check_fail h_err_mem

private theorem evalAtomAligned_eventually_to_sync_of_interpretExpression_eventually
    (space : Space) (dispatch : GroundedDispatch)
    (h_interp_eventual : ∀ atom type_ b r,
      InterpretExpressionAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretExpressionSync space dispatch fuel atom type_ b r) :
    ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r := by
  intro atom type_ b r h
  match h with
  | .empty_or_error atom type_ b h_empty =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (EvalAtomSync.empty_or_error n atom type_ b h_empty)
  | .type_pass atom type_ b h_not_empty h_pass =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (EvalAtomSync.type_pass n atom type_ b h_not_empty h_pass)
  | .type_cast atom type_ b r h_not_empty h_not_pass h_cast_branch h_result_eventual =>
      obtain ⟨fuel0, h_result_eventual⟩ := h_result_eventual
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact EvalAtomSync.type_cast n atom type_ b r
            h_not_empty h_not_pass h_cast_branch
            (h_result_eventual n (Nat.succ_le_succ_iff.mp hfuel))
  | .interpret_success atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_not_error =>
      obtain ⟨fuel0, h_interp_eventual⟩ := h_interp_eventual atom type_ b r h_interp
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact EvalAtomSync.interpret_success n atom type_ b r
            h_not_empty h_not_pass h_expr h_not_unit
            (h_interp_eventual n (Nat.succ_le_succ_iff.mp hfuel))
            h_not_error
  | .interpret_error atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_is_error h_all_errors =>
      obtain ⟨fuel0, h_interp_eventual⟩ := h_interp_eventual atom type_ b r h_interp
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have h_only_errors :
              OnlyErrorsAt (interpretExpression space dispatch atom type_ b n) := by
            intro r' hr'
            exact h_all_errors r'
              (interpretExpression_sound space dispatch atom type_ b n r' hr')
          exact EvalAtomSync.interpret_error n atom type_ b r
            h_not_empty h_not_pass h_expr h_not_unit
            (h_interp_eventual n (Nat.succ_le_succ_iff.mp hfuel))
            h_is_error h_only_errors

private structure AllAlignedEventuallyToSync (space : Space) (dispatch : GroundedDispatch) : Prop where
  evalAtom :
    ∀ atom type_ b r,
      EvalAtomAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        EvalAtomSync space dispatch fuel atom type_ b r
  interpretExpression :
    ∀ atom type_ b r,
      InterpretExpressionAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretExpressionSync space dispatch fuel atom type_ b r
  interpretFunction :
    ∀ atom opType retType b r,
      InterpretFunctionAligned space dispatch atom opType retType b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretFunctionSync space dispatch fuel atom opType b r
  interpretArgs :
    ∀ args types b r,
      InterpretArgsAligned space dispatch args types b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretArgsSync space dispatch fuel args types b r
  interpretTuple :
    ∀ atom b r,
      InterpretTupleAligned space dispatch atom b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        InterpretTupleSync space dispatch fuel atom b r
  mettaCall :
    ∀ atom type_ b r,
      MettaCallAligned space dispatch atom type_ b r →
      ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
        MettaCallSync space dispatch fuel atom type_ b r

mutual

private theorem evalAtomAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : EvalAtomAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      EvalAtomSync space dispatch fuel atom type_ b r := by
  match h with
  | .empty_or_error atom type_ b h_empty =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (EvalAtomSync.empty_or_error n atom type_ b h_empty)
  | .type_pass atom type_ b h_not_empty h_pass =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (EvalAtomSync.type_pass n atom type_ b h_not_empty h_pass)
  | .type_cast atom type_ b r h_not_empty h_not_pass h_cast_branch h_result_eventual =>
      obtain ⟨fuel0, h_result_eventual⟩ := h_result_eventual
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact EvalAtomSync.type_cast n atom type_ b r
            h_not_empty h_not_pass h_cast_branch
            (h_result_eventual n (Nat.succ_le_succ_iff.mp hfuel))
  | .interpret_success atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_not_error =>
      obtain ⟨fuel0, h_interp_eventual⟩ :=
        interpretExpressionAligned_eventually_to_sync space dispatch h_interp
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact EvalAtomSync.interpret_success n atom type_ b r
            h_not_empty h_not_pass h_expr h_not_unit
            (h_interp_eventual n (Nat.succ_le_succ_iff.mp hfuel))
            h_not_error
  | .interpret_error atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_is_error h_all_errors =>
      obtain ⟨fuel0, h_interp_eventual⟩ :=
        interpretExpressionAligned_eventually_to_sync space dispatch h_interp
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have h_only_errors :
              OnlyErrorsAt (interpretExpression space dispatch atom type_ b n) := by
            intro r' hr
            exact h_all_errors r'
              (interpretExpression_sound space dispatch atom type_ b n r' hr)
          exact EvalAtomSync.interpret_error n atom type_ b r
            h_not_empty h_not_pass h_expr h_not_unit
            (h_interp_eventual n (Nat.succ_le_succ_iff.mp hfuel))
            h_is_error h_only_errors

private theorem interpretExpressionAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretExpressionAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      InterpretExpressionSync space dispatch fuel atom type_ b r := by
  match h with
  | .function_path atom type_ b op args funcType retType b' interpResult callResult
      h_shape h_op_type h_is_func h_check_eventual h_ret h_interp h_call =>
      obtain ⟨fuelCheck, h_check_eventual⟩ := h_check_eventual
      obtain ⟨fuelInterp, h_interp_eventual⟩ :=
        interpretFunctionAligned_eventually_to_sync space dispatch h_interp
      obtain ⟨fuelCall, h_call_eventual⟩ :=
        mettaCallAligned_eventually_to_sync space dispatch h_call
      let fuel0 := max fuelCheck (max fuelInterp fuelCall)
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_fuel0 : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
          have hn_check : n ≥ fuelCheck := by
            exact le_trans (Nat.le_max_left fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          have hn_interp : n ≥ fuelInterp := by
            exact le_trans (Nat.le_max_left fuelInterp fuelCall) <|
              le_trans (Nat.le_max_right fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          have hn_call : n ≥ fuelCall := by
            exact le_trans (Nat.le_max_right fuelInterp fuelCall) <|
              le_trans (Nat.le_max_right fuelCheck (max fuelInterp fuelCall)) hn_fuel0
          obtain ⟨succs, h_check, h_check_b⟩ := h_check_eventual n hn_check
          exact InterpretExpressionSync.function_path n atom type_ b op args funcType b'
            interpResult callResult succs h_shape h_op_type h_is_func h_check h_check_b
            (h_interp_eventual n hn_interp)
            (by simpa [h_ret, beq_iff_eq] using h_call_eventual n hn_call)
  | .tuple_path atom type_ b tupleResult callResult h_has_non_func h_tuple h_call =>
      obtain ⟨fuelTuple, h_tuple_eventual⟩ :=
        interpretTupleAligned_eventually_to_sync space dispatch h_tuple
      obtain ⟨fuelCall, h_call_eventual⟩ :=
        mettaCallAligned_eventually_to_sync space dispatch h_call
      have h_shape_ex : ∃ op args, atom = .expression (op :: args) := by
        cases h_tuple with
        | singleton a b r h_eval =>
            exact ⟨a, [], rfl⟩
        | head_error hd tl b headResult h_tl_nonempty h_head h_err =>
            exact ⟨hd, tl, rfl⟩
        | tail_error hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
            exact ⟨hd, tl, rfl⟩
        | success hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
            exact ⟨hd, tl, rfl⟩
      obtain ⟨op, args, h_shape⟩ := h_shape_ex
      have h_has_non_func_bool :
          ((getAtomTypes space op).any fun t =>
            !isFunctionType t || t == Atom.undefinedType) = true := by
        simpa [h_shape, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] using h_has_non_func
      refine ⟨max fuelTuple fuelCall + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelTuple fuelCall := Nat.succ_le_succ_iff.mp hfuel
          have hn_tuple : n ≥ fuelTuple := le_trans (Nat.le_max_left fuelTuple fuelCall) hn_max
          have hn_call : n ≥ fuelCall := le_trans (Nat.le_max_right fuelTuple fuelCall) hn_max
          exact InterpretExpressionSync.tuple_path n atom type_ b op args tupleResult callResult
            h_shape h_has_non_func_bool
            (h_tuple_eventual n hn_tuple)
            (h_call_eventual n hn_call)
  | .op_type_error atom type_ b op args errAtom failedType h_shape
      h_all_fail_eventual h_no_non_func h_failed_type h_failed_func h_check_fail_eventual =>
      obtain ⟨fuelAll, h_all_fail_eventual⟩ := h_all_fail_eventual
      obtain ⟨fuelFail, h_check_fail_eventual⟩ := h_check_fail_eventual
      refine ⟨max fuelAll fuelFail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelAll fuelFail := Nat.succ_le_succ_iff.mp hfuel
          have hn_all : n ≥ fuelAll := le_trans (Nat.le_max_left fuelAll fuelFail) hn_max
          have hn_fail : n ≥ fuelFail := le_trans (Nat.le_max_right fuelAll fuelFail) hn_max
          obtain ⟨errs, h_check_fail, h_err_mem⟩ := h_check_fail_eventual n hn_fail
          have h_has_non_func_false :
              ((getAtomTypes space op).any fun t =>
                !isFunctionType t || t == Atom.undefinedType) = false := by
            by_cases h_any :
                ((getAtomTypes space op).any fun t =>
                  !isFunctionType t || t == Atom.undefinedType) = true
            · have h_exists :
                  ∃ t ∈ getAtomTypes space op,
                    isFunctionType t = false ∨ t = Atom.undefinedType := by
                simpa [List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] using h_any
              rcases h_exists with ⟨t, h_t_mem, h_bad⟩
              rcases h_no_non_func t h_t_mem with ⟨h_t_func, h_t_not_undef⟩
              cases h_bad with
              | inl h_not_func =>
                  have : False := by
                    simp [h_t_func] at h_not_func
                  exact this.elim
              | inr h_undef =>
                  exact (h_t_not_undef h_undef).elim
            · cases h_bool :
                  ((getAtomTypes space op).any fun t =>
                    !isFunctionType t || t == Atom.undefinedType) <;> simp_all
          have h_all_fail_bool :
              ((getAtomTypes space op).all fun funcType =>
                if isFunctionType funcType then
                  match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
                  | .inl _ => true
                  | .inr _ => false
                else true) = true := by
            rw [List.all_eq_true]
            intro ft h_ft_mem
            by_cases h_is_func : isFunctionType ft = true
            · obtain ⟨errs', h_fail⟩ := h_all_fail_eventual n hn_all ft h_ft_mem h_is_func
              simp [h_is_func, h_fail]
            · simp [h_is_func]
          exact InterpretExpressionSync.op_type_error n atom type_ b op args failedType errs errAtom
            h_shape h_has_non_func_false h_all_fail_bool
            h_failed_type h_failed_func h_check_fail h_err_mem

private theorem interpretFunctionAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {atom opType retType : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretFunctionAligned space dispatch atom opType retType b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      InterpretFunctionSync space dispatch fuel atom opType b r := by
  match h with
  | .head_error atom opType retType b op args headResult h_shape h_head h_err =>
      obtain ⟨fuel0, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact InterpretFunctionSync.head_error n atom opType b op args headResult
            h_shape (h_head_eventual n (Nat.succ_le_succ_iff.mp hfuel)) h_err
  | .head_ok_tail_error atom opType retType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_err =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretArgsAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretFunctionSync.head_ok_tail_error n atom opType b op args argTypes
            headResult tailResult h_shape h_arg_types
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_err
  | .head_ok_tail_ok atom opType retType b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_ok =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretArgsAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretFunctionSync.head_ok_tail_ok n atom opType b op args argTypes
            headResult tailResult h_shape h_arg_types
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_ok

private theorem interpretArgsAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {args types : List Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretArgsAligned space dispatch args types b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      InterpretArgsSync space dispatch fuel args types b r := by
  match h with
  | .nil b =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (InterpretArgsSync.nil (space := space) (dispatch := dispatch) n b)
  | .head_changed_error a as t ts b headResult h_head h_err h_changed =>
      obtain ⟨fuel0, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
          exact InterpretArgsSync.head_changed_error n a as t ts b headResult
            (h_head_eventual n hn) h_err h_changed
  | .cons_tail_error a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_err =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretArgsAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretArgsSync.cons_tail_error n a as t ts b headResult tailResult
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_err
  | .cons_ok a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_ok =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretArgsAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretArgsSync.cons_ok n a as t ts b headResult tailResult
            (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_ok

private theorem interpretTupleAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {atom : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretTupleAligned space dispatch atom b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      InterpretTupleSync space dispatch fuel atom b r := by
  match h with
  | .singleton a b r h_eval =>
      obtain ⟨fuel0, h_eval_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_eval
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact InterpretTupleSync.singleton n a b r
            (h_eval_eventual n (Nat.succ_le_succ_iff.mp hfuel))
  | .head_error hd tl b headResult h_tl_nonempty h_head h_err =>
      obtain ⟨fuel0, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact InterpretTupleSync.head_error n hd tl b headResult
            h_tl_nonempty (h_head_eventual n (Nat.succ_le_succ_iff.mp hfuel)) h_err
  | .tail_error hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretTupleAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretTupleSync.tail_error n hd tl b headResult tailResult
            h_tl_nonempty (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_err
  | .success hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
      obtain ⟨fuelHead, h_head_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_head
      obtain ⟨fuelTail, h_tail_eventual⟩ :=
        interpretTupleAligned_eventually_to_sync space dispatch h_tail
      refine ⟨max fuelHead fuelTail + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelHead fuelTail := Nat.succ_le_succ_iff.mp hfuel
          have hn_head : n ≥ fuelHead := le_trans (Nat.le_max_left fuelHead fuelTail) hn_max
          have hn_tail : n ≥ fuelTail := le_trans (Nat.le_max_right fuelHead fuelTail) hn_max
          exact InterpretTupleSync.success n hd tl b headResult tailResult
            h_tl_nonempty (h_head_eventual n hn_head) h_head_ok
            (h_tail_eventual n hn_tail) h_tail_ok

private theorem mettaCallAligned_eventually_to_sync
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : MettaCallAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      MettaCallSync space dispatch fuel atom type_ b r := by
  match h with
  | .error_passthrough atom type_ b h_err =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using (MettaCallSync.error_passthrough n atom type_ b h_err)
  | .grounded_ok atom type_ b op args nativeResults nativeResult merged finalResult
      h_shape h_exec h_not_error h_native h_native_mem h_merge_eventual h_recurse =>
      obtain ⟨fuelMerge, h_merge_eventual⟩ := h_merge_eventual
      obtain ⟨fuelEval, h_eval_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_recurse
      refine ⟨max fuelMerge fuelEval + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_max : n ≥ max fuelMerge fuelEval := Nat.succ_le_succ_iff.mp hfuel
          have hn_merge : n ≥ fuelMerge := le_trans (Nat.le_max_left fuelMerge fuelEval) hn_max
          have hn_eval : n ≥ fuelEval := le_trans (Nat.le_max_right fuelMerge fuelEval) hn_max
          exact MettaCallSync.grounded_ok n atom type_ b op args nativeResults nativeResult
            merged finalResult h_shape h_exec h_not_error h_native h_native_mem
            (h_merge_eventual n hn_merge) (h_eval_eventual n hn_eval)
  | .grounded_runtime_error atom type_ b op args msg h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_runtime_error n atom type_ b op args msg
              h_shape h_exec h_not_error h_native)
  | .grounded_no_reduce atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_no_reduce n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .grounded_incorrect_arg atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_incorrect_arg n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .grounded_empty_results atom type_ b op args h_shape h_exec h_not_error h_native =>
      refine ⟨1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          simpa using
            (MettaCallSync.grounded_empty_results n atom type_ b op args
              h_shape h_exec h_not_error h_native)
  | .equation_match atom type_ b rhs applied queryBindings merged finalResult
      h_not_error h_not_grounded h_query_eventual h_merge_eventual h_no_loop
      h_apply_stable h_recurse =>
      obtain ⟨fuelQuery, h_query_eventual⟩ := h_query_eventual
      obtain ⟨fuelMerge, h_merge_eventual⟩ := h_merge_eventual
      obtain ⟨fuelApply, h_apply_stable⟩ := h_apply_stable
      obtain ⟨fuelEval, h_eval_eventual⟩ :=
        evalAtomAligned_eventually_to_sync space dispatch h_recurse
      let fuel0 := max (max fuelQuery fuelMerge) (max fuelApply fuelEval)
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          have hn_fuel0 : n ≥ fuel0 := Nat.succ_le_succ_iff.mp hfuel
          have hn_query : n ≥ fuelQuery := by
            exact le_trans (Nat.le_max_left fuelQuery fuelMerge) <|
              le_trans (Nat.le_max_left (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_merge : n ≥ fuelMerge := by
            exact le_trans (Nat.le_max_right fuelQuery fuelMerge) <|
              le_trans (Nat.le_max_left (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_apply : n ≥ fuelApply := by
            exact le_trans (Nat.le_max_left fuelApply fuelEval) <|
              le_trans (Nat.le_max_right (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have hn_eval : n ≥ fuelEval := by
            exact le_trans (Nat.le_max_right fuelApply fuelEval) <|
              le_trans (Nat.le_max_right (max fuelQuery fuelMerge) (max fuelApply fuelEval)) hn_fuel0
          have h_apply_eq : merged.apply rhs n = applied := h_apply_stable n hn_apply
          exact MettaCallSync.equation_match n atom type_ b rhs queryBindings merged finalResult
            h_not_error h_not_grounded
            (h_query_eventual n hn_query)
            (h_merge_eventual n hn_merge)
            h_no_loop
            (by simpa [h_apply_eq] using h_eval_eventual n hn_eval)
  | .no_match atom type_ b h_not_error h_not_grounded h_no_eqs_eventual =>
      obtain ⟨fuel0, h_no_eqs_eventual⟩ := h_no_eqs_eventual
      refine ⟨fuel0 + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero => cases hfuel
      | succ n =>
          exact MettaCallSync.no_match n atom type_ b h_not_error h_not_grounded
            (h_no_eqs_eventual n (Nat.succ_le_succ_iff.mp hfuel))

end

private theorem allAlignedEventuallyToSync
    (space : Space) (dispatch : GroundedDispatch) :
    AllAlignedEventuallyToSync space dispatch := by
  refine
    { evalAtom := ?_
      interpretExpression := ?_
      interpretFunction := ?_
      interpretArgs := ?_
      interpretTuple := ?_
      mettaCall := ?_ }
  · intro atom type_ b r h
    exact evalAtomAligned_eventually_to_sync space dispatch h
  · intro atom type_ b r h
    exact interpretExpressionAligned_eventually_to_sync space dispatch h
  · intro atom opType retType b r h
    exact interpretFunctionAligned_eventually_to_sync space dispatch h
  · intro args types b r h
    exact interpretArgsAligned_eventually_to_sync space dispatch h
  · intro atom b r h
    exact interpretTupleAligned_eventually_to_sync space dispatch h
  · intro atom type_ b r h
    exact mettaCallAligned_eventually_to_sync space dispatch h

private theorem evalAtomAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : EvalAtomAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ evalAtom space dispatch atom type_ b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).evalAtom atom type_ b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (evalAtom_exact_at (space := space) (dispatch := dispatch)
    (atom := atom) (type_ := type_) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

private theorem interpretExpressionAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretExpressionAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretExpression space dispatch atom type_ b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).interpretExpression atom type_ b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (interpretExpression_exact_at (space := space) (dispatch := dispatch)
    (atom := atom) (type_ := type_) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

private theorem interpretFunctionAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {atom opType retType : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretFunctionAligned space dispatch atom opType retType b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretFunction space dispatch atom opType b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).interpretFunction atom opType retType b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (interpretFunction_exact_at (space := space) (dispatch := dispatch)
    (atom := atom) (opType := opType) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

private theorem interpretArgsAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {args types : List Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretArgsAligned space dispatch args types b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretArgs space dispatch args types b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).interpretArgs args types b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (interpretArgs_exact_at (space := space) (dispatch := dispatch)
    (args := args) (types := types) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

private theorem interpretTupleAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {atom : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretTupleAligned space dispatch atom b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretTuple space dispatch atom b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).interpretTuple atom b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (interpretTuple_exact_at (space := space) (dispatch := dispatch)
    (atom := atom) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

private theorem mettaCallAligned_eventually_reaches
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : MettaCallAligned space dispatch atom type_ b r) :
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ mettaCall space dispatch atom type_ b fuel := by
  obtain ⟨fuel0, h_sync⟩ := (allAlignedEventuallyToSync space dispatch).mettaCall atom type_ b r h
  refine ⟨fuel0, ?_⟩
  intro fuel hfuel
  exact (mettaCall_exact_at (space := space) (dispatch := dispatch)
    (atom := atom) (type_ := type_) (b := b) (r := r) (fuel := fuel)).2
      (h_sync fuel hfuel)

mutual

private theorem evalAtomAligned_to_EvalAtom
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : EvalAtomAligned space dispatch atom type_ b r) :
    EvalAtom space dispatch atom type_ b r := by
  match h with
  | .empty_or_error atom type_ b h_empty =>
      exact .empty_or_error atom type_ b h_empty
  | .type_pass atom type_ b h_not_empty h_pass =>
      exact .type_pass atom type_ b h_not_empty h_pass
  | .type_cast atom type_ b r h_not_empty h_not_pass h_cast_branch h_result_eventual =>
      obtain ⟨fuel0, h_result_eventual⟩ := h_result_eventual
      exact .type_cast atom type_ b r fuel0
        h_not_empty h_not_pass h_cast_branch
        (h_result_eventual fuel0 le_rfl)
  | .interpret_success atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_not_error =>
      exact .interpret_success atom type_ b r
        h_not_empty h_not_pass h_expr h_not_unit
        (interpretExpressionAligned_to_InterpretExpression space dispatch h_interp)
        h_not_error
  | .interpret_error atom type_ b r h_not_empty h_not_pass h_expr h_not_unit h_interp h_is_error h_all_errors =>
      exact .interpret_error atom type_ b r
        h_not_empty h_not_pass h_expr h_not_unit
        (interpretExpressionAligned_to_InterpretExpression space dispatch h_interp)
        h_is_error

private theorem interpretExpressionAligned_to_InterpretExpression
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretExpressionAligned space dispatch atom type_ b r) :
    InterpretExpression space dispatch atom type_ b r := by
  match h with
  | .function_path atom type_ b op args funcType retType b' interpResult callResult
      h_shape h_op_type h_is_func h_check_eventual h_ret h_interp h_call =>
      obtain ⟨fuel0, h_check_eventual⟩ := h_check_eventual
      obtain ⟨succs, h_check, h_check_b⟩ := h_check_eventual fuel0 le_rfl
      exact .function_path atom type_ b op args funcType retType b' interpResult callResult fuel0
        h_shape h_op_type h_is_func succs h_check h_check_b h_ret
        (interpretFunctionAligned_to_InterpretFunction space dispatch h_interp)
        (mettaCallAligned_to_MettaCall space dispatch h_call)
  | .tuple_path atom type_ b tupleResult callResult h_has_non_func h_tuple h_call =>
      exact .tuple_path atom type_ b tupleResult callResult
        h_has_non_func
        (interpretTupleAligned_to_InterpretTuple space dispatch h_tuple)
        (mettaCallAligned_to_MettaCall space dispatch h_call)
  | .op_type_error atom type_ b op args errAtom failedType h_shape
      h_all_fail_eventual h_no_non_func h_failed_type h_failed_func h_check_fail_eventual =>
      obtain ⟨fuelAll, h_all_fail_eventual⟩ := h_all_fail_eventual
      obtain ⟨fuelFail, h_check_fail_eventual⟩ := h_check_fail_eventual
      let fuel0 := max fuelAll fuelFail
      obtain ⟨errs, h_check_fail, h_err_mem⟩ := h_check_fail_eventual fuel0 (Nat.le_max_right fuelAll fuelFail)
      exact .op_type_error atom type_ b op args errAtom fuel0 failedType errs
        h_shape
        (by
          intro ft h_ft_mem h_is_func
          exact h_all_fail_eventual fuel0 (Nat.le_max_left fuelAll fuelFail) ft h_ft_mem h_is_func)
        h_no_non_func h_failed_type h_failed_func h_check_fail h_err_mem

private theorem interpretFunctionAligned_to_InterpretFunction
    (space : Space) (dispatch : GroundedDispatch)
    {atom opType retTypeIn retTypeOut : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretFunctionAligned space dispatch atom opType retTypeIn b r) :
    InterpretFunction space dispatch atom opType retTypeOut b r := by
  match h with
  | .head_error atom opType retTypeIn b op args headResult h_shape h_head h_err =>
      exact .head_error atom opType retTypeOut b op args headResult
        h_shape (evalAtomAligned_to_EvalAtom space dispatch h_head) h_err
  | .head_ok_tail_error atom opType retTypeIn b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_err =>
      exact .head_ok_tail_error atom opType retTypeOut b op args argTypes headResult tailResult
        h_shape h_arg_types
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretArgsAligned_to_InterpretArgs space dispatch h_tail)
        h_tail_err
  | .head_ok_tail_ok atom opType retTypeIn b op args argTypes headResult tailResult
      h_shape h_arg_types h_head h_head_ok h_tail h_tail_ok =>
      exact .head_ok_tail_ok atom opType retTypeOut b op args argTypes headResult tailResult
        h_shape h_arg_types
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretArgsAligned_to_InterpretArgs space dispatch h_tail)
        h_tail_ok

private theorem interpretArgsAligned_to_InterpretArgs
    (space : Space) (dispatch : GroundedDispatch)
    {args types : List Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretArgsAligned space dispatch args types b r) :
    InterpretArgs space dispatch args types b r := by
  match h with
  | .nil b =>
      exact .nil (space := space) (dispatch := dispatch) (b := b)
  | .head_changed_error a as t ts b headResult h_head h_err h_changed =>
      exact .head_changed_error a as t ts b headResult
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_err h_changed
  | .cons_tail_error a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_err =>
      exact .cons_tail_error a as t ts b headResult tailResult
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretArgsAligned_to_InterpretArgs space dispatch h_tail) h_tail_err
  | .cons_ok a as t ts b headResult tailResult h_head h_head_ok h_tail h_tail_ok =>
      exact .cons_ok a as t ts b headResult tailResult
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretArgsAligned_to_InterpretArgs space dispatch h_tail) h_tail_ok

private theorem interpretTupleAligned_to_InterpretTuple
    (space : Space) (dispatch : GroundedDispatch)
    {atom : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretTupleAligned space dispatch atom b r) :
    InterpretTuple space dispatch atom b r := by
  match h with
  | .singleton a b r h_eval =>
      exact .singleton a b r (evalAtomAligned_to_EvalAtom space dispatch h_eval)
  | .head_error hd tl b headResult h_tl_nonempty h_head h_err =>
      exact .head_error hd tl b headResult h_tl_nonempty
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_err
  | .tail_error hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_err =>
      exact .tail_error hd tl b headResult tailResult h_tl_nonempty
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretTupleAligned_to_InterpretTuple space dispatch h_tail) h_tail_err
  | .success hd tl b headResult tailResult h_tl_nonempty h_head h_head_ok h_tail h_tail_ok =>
      exact .success hd tl b headResult tailResult h_tl_nonempty
        (evalAtomAligned_to_EvalAtom space dispatch h_head) h_head_ok
        (interpretTupleAligned_to_InterpretTuple space dispatch h_tail) h_tail_ok

private theorem mettaCallAligned_to_MettaCall
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : MettaCallAligned space dispatch atom type_ b r) :
    MettaCall space dispatch atom type_ b r := by
  match h with
  | .error_passthrough atom type_ b h_err =>
      exact .error_passthrough atom type_ b h_err
  | .grounded_ok atom type_ b op args nativeResults nativeResult merged finalResult
      h_shape h_exec h_not_error h_native h_native_mem h_merge_eventual h_recurse =>
      obtain ⟨fuel0, h_merge_eventual⟩ := h_merge_eventual
      exact .grounded_ok atom type_ b op args nativeResults nativeResult merged finalResult fuel0
        h_shape h_exec h_not_error h_native h_native_mem
        (h_merge_eventual fuel0 le_rfl)
        (evalAtomAligned_to_EvalAtom space dispatch h_recurse)
  | .grounded_runtime_error atom type_ b op args msg h_shape h_exec h_not_error h_native =>
      exact .grounded_runtime_error atom type_ b op args msg h_shape h_exec h_not_error h_native
  | .grounded_no_reduce atom type_ b op args h_shape h_exec h_not_error h_native =>
      exact .grounded_no_reduce atom type_ b op args h_shape h_exec h_not_error h_native
  | .grounded_incorrect_arg atom type_ b op args h_shape h_exec h_not_error h_native =>
      exact .grounded_incorrect_arg atom type_ b op args h_shape h_exec h_not_error h_native
  | .grounded_empty_results atom type_ b op args h_shape h_exec h_not_error h_native =>
      exact .grounded_empty_results atom type_ b op args h_shape h_exec h_not_error h_native
  | .equation_match atom type_ b rhs applied queryBindings merged finalResult
      h_not_error h_not_grounded h_query_eventual h_merge_eventual h_no_loop
      h_apply_stable h_recurse =>
      obtain ⟨fuelQuery, h_query_eventual⟩ := h_query_eventual
      obtain ⟨fuelMerge, h_merge_eventual⟩ := h_merge_eventual
      obtain ⟨fuelApply, h_apply_stable⟩ := h_apply_stable
      let fuel0 := max (max fuelQuery fuelMerge) fuelApply
      have h_query : (rhs, queryBindings) ∈ queryEquations space atom fuel0 := by
        exact h_query_eventual fuel0 <|
          le_trans (Nat.le_max_left fuelQuery fuelMerge) (Nat.le_max_left (max fuelQuery fuelMerge) fuelApply)
      have h_merge : merged ∈ mergeBindings queryBindings b fuel0 := by
        exact h_merge_eventual fuel0 <|
          le_trans (Nat.le_max_right fuelQuery fuelMerge) (Nat.le_max_left (max fuelQuery fuelMerge) fuelApply)
      have h_apply_eq : merged.apply rhs fuel0 = applied := by
        exact h_apply_stable fuel0 (Nat.le_max_right (max fuelQuery fuelMerge) fuelApply)
      exact .equation_match atom type_ b rhs queryBindings merged finalResult fuel0
        h_not_error h_not_grounded h_query h_merge h_no_loop
        (by simpa [h_apply_eq] using evalAtomAligned_to_EvalAtom space dispatch h_recurse)
  | .no_match atom type_ b h_not_error h_not_grounded h_no_eqs_eventual =>
      obtain ⟨fuel0, h_no_eqs_eventual⟩ := h_no_eqs_eventual
      exact .no_match atom type_ b fuel0 h_not_error h_not_grounded
        (h_no_eqs_eventual fuel0 le_rfl)

end

private theorem evalAtomAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : EvalAtomAligned space dispatch atom type_ b r) :
    EvalAtom space dispatch atom type_ b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ evalAtom space dispatch atom type_ b fuel := by
  exact ⟨evalAtomAligned_to_EvalAtom space dispatch h,
    evalAtomAligned_eventually_reaches space dispatch h⟩

private theorem interpretExpressionAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretExpressionAligned space dispatch atom type_ b r) :
    InterpretExpression space dispatch atom type_ b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretExpression space dispatch atom type_ b fuel := by
  exact ⟨interpretExpressionAligned_to_InterpretExpression space dispatch h,
    interpretExpressionAligned_eventually_reaches space dispatch h⟩

private theorem interpretFunctionAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {atom opType retType : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretFunctionAligned space dispatch atom opType retType b r) :
    InterpretFunction space dispatch atom opType retType b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretFunction space dispatch atom opType b fuel := by
  exact ⟨interpretFunctionAligned_to_InterpretFunction space dispatch h,
    interpretFunctionAligned_eventually_reaches space dispatch h⟩

private theorem interpretArgsAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {args types : List Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretArgsAligned space dispatch args types b r) :
    InterpretArgs space dispatch args types b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretArgs space dispatch args types b fuel := by
  exact ⟨interpretArgsAligned_to_InterpretArgs space dispatch h,
    interpretArgsAligned_eventually_reaches space dispatch h⟩

private theorem interpretTupleAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {atom : Atom} {b : Bindings} {r : ResultPair}
    (h : InterpretTupleAligned space dispatch atom b r) :
    InterpretTuple space dispatch atom b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ interpretTuple space dispatch atom b fuel := by
  exact ⟨interpretTupleAligned_to_InterpretTuple space dispatch h,
    interpretTupleAligned_eventually_reaches space dispatch h⟩

private theorem mettaCallAligned_public_bridge
    (space : Space) (dispatch : GroundedDispatch)
    {atom type_ : Atom} {b : Bindings} {r : ResultPair}
    (h : MettaCallAligned space dispatch atom type_ b r) :
    MettaCall space dispatch atom type_ b r ∧
    ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
      r ∈ mettaCall space dispatch atom type_ b fuel := by
  exact ⟨mettaCallAligned_to_MettaCall space dispatch h,
    mettaCallAligned_eventually_reaches space dispatch h⟩

end Mettapedia.Languages.MeTTa.HE
