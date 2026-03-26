import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# HE Evaluator Soundness

Soundness of the 6 mutual evaluation functions in `Eval.lean` against
the declarative spec in `EvalSpec.lean`. Each theorem states: every result
in the evaluator's output has a valid `EvalSpec` derivation tree.

## Architecture
- Combined `AllSound fuel` proposition (6-way conjunction)
- Plain `Nat.rec` induction on `fuel` (evaluator at `n+1` calls sub-functions at `n`)
- Individual theorems projected from the combined result
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
      (h_all_errors : ∀ r' : ResultPair,
        r' ∈ interpretExpression space dispatch atom type_ b n →
        isErrorAtom r'.1 = true) :
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

/-- Private synchronous model for `mettaCall`. -/
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

end Mettapedia.Languages.MeTTa.HE
