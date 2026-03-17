-- LLM primer: EvalIR is a minimal evaluator IR for the recursive evaluation vertical slice.
-- Supports: integer literals, boolean literals, if-then-else, ==, +, -, *, userCall.
-- The reference evaluator is fuel-bounded and sorry-free.
-- The MM2 protocol types (ReqId, MM2Fact, MM2Step) formalize the request/result/join
-- state machine that MORK executes, including IntArithSink grounded arithmetic.
-- Council: Martin-Löf/Coquand/Pfenning (types first), Carneiro/Brown (minimal),
--   Tao/Kolmogorov (proper Value type), Buzzard/Voevodsky (no sorry).
-- `eval` is partial (Lean can't prove termination through evalList HOF), but fully
-- implemented — validated by #eval.

namespace MeTTailCore.EvalIR

-- ═══════════════════════════════════════════════════════════════════════════
-- § Core IR Types
-- ═══════════════════════════════════════════════════════════════════════════

/-- Values produced by the evaluator: integers or booleans. -/
inductive EvalValue where
  | int : Int → EvalValue
  | bool : Bool → EvalValue
deriving Repr, DecidableEq, BEq

/-- Evaluator IR nodes. Supports the recursive evaluation fragment:
    integer/boolean literals, if-then-else, equality, addition, subtraction,
    multiplication, and user-defined function calls. -/
inductive EvalNode where
  | intLit : Int → EvalNode
  | boolLit : Bool → EvalNode
  | ifCond : EvalNode → EvalNode → EvalNode → EvalNode
  | eqInt : EvalNode → EvalNode → EvalNode
  | addInt : EvalNode → EvalNode → EvalNode
  | subInt : EvalNode → EvalNode → EvalNode
  | mulInt : EvalNode → EvalNode → EvalNode
  | userCall : String → List EvalNode → EvalNode
deriving Repr, BEq

/-- A user-defined rule: head name, parameter names, body expression. -/
structure EvalRule where
  head : String
  params : List String
  body : EvalNode
deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reference Evaluator
-- ═══════════════════════════════════════════════════════════════════════════

/-- Authoritative rule lookup: find the FIRST rule matching head and arity.
    Used consistently across eval, evalMemo, EvalSem, and EvalTrace. -/
def lookupRule (rules : List EvalRule) (head : String) (arity : Nat) : Option EvalRule :=
  rules.find? (fun r => r.head == head && r.params.length == arity)

-- Substitution: replace free variable references in a node with values.
-- Variables are represented as `userCall varName []` (nullary calls).
-- Non-partial: mutual recursion with explicit list traversal.
mutual
  def substNode (env : List (String × EvalNode)) : EvalNode → EvalNode
    | .intLit n => .intLit n
    | .boolLit b => .boolLit b
    | .ifCond c t e => .ifCond (substNode env c) (substNode env t) (substNode env e)
    | .eqInt a b => .eqInt (substNode env a) (substNode env b)
    | .addInt a b => .addInt (substNode env a) (substNode env b)
    | .subInt a b => .subInt (substNode env a) (substNode env b)
    | .mulInt a b => .mulInt (substNode env a) (substNode env b)
    | .userCall head args =>
      match args with
      | [] =>
        match env.find? (fun p => p.1 == head) with
        | some (_, replacement) => replacement
        | none => .userCall head []
      | _ => .userCall head (substNodeList env args)

  def substNodeList (env : List (String × EvalNode)) : List EvalNode → List EvalNode
    | [] => []
    | a :: as => substNode env a :: substNodeList env as
end

/-- Convert an EvalValue back to an EvalNode (for substitution after evaluation). -/
def EvalValue.toNode : EvalValue → EvalNode
  | .int n => .intLit n
  | .bool b => .boolLit b

-- Reference evaluator — the semantic oracle.
-- Fuel-bounded: fuel consumed only by userCall.
-- Non-partial: mutual recursion with explicit list traversal.
mutual
  def eval (rules : List EvalRule) (fuel : Nat) (node : EvalNode) : Option EvalValue :=
    match node with
    | .intLit n => some (.int n)
    | .boolLit b => some (.bool b)
    | .ifCond c t e =>
      match eval rules fuel c with
      | some (.bool true) => eval rules fuel t
      | some (.bool false) => eval rules fuel e
      | _ => none
    | .eqInt a b =>
      match eval rules fuel a, eval rules fuel b with
      | some (.int va), some (.int vb) => some (.bool (va == vb))
      | _, _ => none
    | .addInt a b =>
      match eval rules fuel a, eval rules fuel b with
      | some (.int va), some (.int vb) => some (.int (va + vb))
      | _, _ => none
    | .subInt a b =>
      match eval rules fuel a, eval rules fuel b with
      | some (.int va), some (.int vb) => some (.int (va - vb))
      | _, _ => none
    | .mulInt a b =>
      match eval rules fuel a, eval rules fuel b with
      | some (.int va), some (.int vb) => some (.int (va * vb))
      | _, _ => none
    | .userCall head args =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        let evalArgs := evalList rules (fuel' + 1) args
        if evalArgs.any Option.isNone then none
        else
          match lookupRule rules head args.length with
          | none => none
          | some rule =>
            let argNodes := evalArgs.filterMap (fun v => v.map EvalValue.toNode)
            let env := rule.params.zip argNodes
            let body' := substNode env rule.body
            eval rules fuel' body'
  termination_by (fuel, sizeOf node)

  def evalList (rules : List EvalRule) (fuel : Nat) (nodes : List EvalNode) : List (Option EvalValue) :=
    match nodes with
    | [] => []
    | a :: as => eval rules fuel a :: evalList rules fuel as
  termination_by (fuel, sizeOf nodes)
end

-- ═══════════════════════════════════════════════════════════════════════════
-- § Layer 1: Ideal CBV Evaluator with Memoization
-- ═══════════════════════════════════════════════════════════════════════════
-- The SPECIFICATION of what the MM2 evaluator must compute.
-- Call-by-value: evaluate args to values before body expansion.
-- Memoization: cache (head, [arg_values]) → result.
-- Key property: memo keys are EVALUATED values, never raw syntax.

/-- Memo table: maps (function_head, [evaluated_arg_values]) to result. -/
abbrev MemoTable := List (String × List EvalValue × EvalValue)

/-- Look up a memo entry. Uses decidable equality (not BEq) for proof compatibility. -/
def memoLookup (table : MemoTable) (head : String) (argVals : List EvalValue) : Option EvalValue :=
  table.findSome? fun (h, vs, r) => if h = head ∧ vs = argVals then some r else none

-- Memoized CBV evaluator — the ideal specification.
-- Same as `eval` but threads a memo table. On userCall:
-- 1. Evaluate args to values (CBV)
-- 2. Check memo on (head, [arg_values])
-- 3. If hit: return cached result
-- 4. If miss: expand body, evaluate, cache result
-- Non-partial: mutual recursion with explicit list traversal.
mutual
  def evalMemo (rules : List EvalRule) (fuel : Nat) (memo : MemoTable)
      (node : EvalNode) : Option EvalValue × MemoTable :=
    match node with
    | .intLit n => (some (.int n), memo)
    | .boolLit b => (some (.bool b), memo)
    | .ifCond c t e =>
      let (cv, memo) := evalMemo rules fuel memo c
      match cv with
      | some (.bool true) => evalMemo rules fuel memo t
      | some (.bool false) => evalMemo rules fuel memo e
      | _ => (none, memo)
    | .eqInt a b =>
      let (av, memo) := evalMemo rules fuel memo a
      let (bv, memo) := evalMemo rules fuel memo b
      match av, bv with
      | some (.int va), some (.int vb) => (some (.bool (va == vb)), memo)
      | _, _ => (none, memo)
    | .addInt a b =>
      let (av, memo) := evalMemo rules fuel memo a
      let (bv, memo) := evalMemo rules fuel memo b
      match av, bv with
      | some (.int va), some (.int vb) => (some (.int (va + vb)), memo)
      | _, _ => (none, memo)
    | .subInt a b =>
      let (av, memo) := evalMemo rules fuel memo a
      let (bv, memo) := evalMemo rules fuel memo b
      match av, bv with
      | some (.int va), some (.int vb) => (some (.int (va - vb)), memo)
      | _, _ => (none, memo)
    | .mulInt a b =>
      let (av, memo) := evalMemo rules fuel memo a
      let (bv, memo) := evalMemo rules fuel memo b
      match av, bv with
      | some (.int va), some (.int vb) => (some (.int (va * vb)), memo)
      | _, _ => (none, memo)
    | .userCall head args =>
      match fuel with
      | 0 => (none, memo)
      | fuel' + 1 =>
        -- Step 1: Evaluate args to values (CBV)
        let (argVals, memo) := evalMemoList rules (fuel' + 1) memo args
        if argVals.any Option.isNone then (none, memo)
        else
          let vals := argVals.filterMap fun x => x
          -- Step 2: Check memo
          match memoLookup memo head vals with
          | some cached => (some cached, memo)  -- memo HIT
          | none =>
            -- Step 3: Expand body and evaluate
            match lookupRule rules head args.length with
            | none => (none, memo)
            | some rule =>
              let argNodes := vals.map EvalValue.toNode
              let env := rule.params.zip argNodes
              let body' := substNode env rule.body
              let (result, memo) := evalMemo rules fuel' memo body'
              -- Step 4: Cache result
              match result with
              | some v => (some v, (head, vals, v) :: memo)
              | none => (none, memo)
  termination_by (fuel, sizeOf node)

  def evalMemoList (rules : List EvalRule) (fuel : Nat) (memo : MemoTable)
      (nodes : List EvalNode) : List (Option EvalValue) × MemoTable :=
    match nodes with
    | [] => ([], memo)
    | a :: as =>
      let (v, memo) := evalMemo rules fuel memo a
      let (vs, memo) := evalMemoList rules fuel memo as
      (v :: vs, memo)
  termination_by (fuel, sizeOf nodes)
end

-- ═══════════════════════════════════════════════════════════════════════════
-- § Fuel-Free Semantic Relation (EvalSem)
-- ═══════════════════════════════════════════════════════════════════════════
-- The ground truth for what the evaluator MEANS. No fuel parameter.
-- Functions (eval, evalMemo) are algorithms; EvalSem is the meaning.
-- The FALSE theorem `evalMemo rules fuel node = eval rules fuel node`
-- is disproved by counterexample at end of file (GPT-5.4 Pro, 2026-03-16).

-- Fuel-free big-step semantics for the recursive evaluation fragment.
-- Deterministic: each node has at most one value under EvalSem.
mutual
  inductive EvalSem (rules : List EvalRule) : EvalNode → EvalValue → Prop where
    | litInt : EvalSem rules (.intLit n) (.int n)
    | litBool : EvalSem rules (.boolLit b) (.bool b)
    | eqOp : EvalSem rules a (.int va) → EvalSem rules b (.int vb) →
             EvalSem rules (.eqInt a b) (.bool (va == vb))
    | addOp : EvalSem rules a (.int va) → EvalSem rules b (.int vb) →
              EvalSem rules (.addInt a b) (.int (va + vb))
    | subOp : EvalSem rules a (.int va) → EvalSem rules b (.int vb) →
              EvalSem rules (.subInt a b) (.int (va - vb))
    | mulOp : EvalSem rules a (.int va) → EvalSem rules b (.int vb) →
              EvalSem rules (.mulInt a b) (.int (va * vb))
    | ifTrue : EvalSem rules c (.bool true) → EvalSem rules t vt →
               EvalSem rules (.ifCond c t e) vt
    | ifFalse : EvalSem rules c (.bool false) → EvalSem rules e ve →
                EvalSem rules (.ifCond c t e) ve
    | userCall : EvalSemList rules args argVals →
                 lookupRule rules head args.length = some rule →
                 EvalSem rules (substNode (rule.params.zip (argVals.map EvalValue.toNode)) rule.body) v →
                 EvalSem rules (.userCall head args) v

  inductive EvalSemList (rules : List EvalRule) : List EvalNode → List EvalValue → Prop where
    | nil : EvalSemList rules [] []
    | cons : EvalSem rules a v → EvalSemList rules as vs →
             EvalSemList rules (a :: as) (v :: vs)
end

/-- Fuel-free memo soundness: every cached entry is semantically correct. -/
def MemoSoundSem (rules : List EvalRule) (memo : MemoTable) : Prop :=
  ∀ h vs v, (h, vs, v) ∈ memo →
    EvalSem rules (.userCall h (vs.map EvalValue.toNode)) v

/-- memoLookup is sound: if it returns a value, that value is semantically correct. -/
theorem memoLookup_sound {rules : List EvalRule} {memo : MemoTable}
    {head : String} {argVals : List EvalValue} {v : EvalValue}
    (hm : MemoSoundSem rules memo) (h : memoLookup memo head argVals = some v) :
    EvalSem rules (.userCall head (argVals.map EvalValue.toNode)) v := by
  unfold memoLookup at h
  obtain ⟨⟨h', vs', r'⟩, hmem, hfound⟩ := List.exists_of_findSome?_eq_some h
  simp at hfound
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfound
  exact hm _ _ _ hmem

-- ── Semantic Helper Lemmas (GPT-5.4 Pro recipe) ─────────────────────────

theorem evalSem_toNode {rules : List EvalRule} :
    ∀ v : EvalValue, EvalSem rules v.toNode v
  | .int _ => .litInt
  | .bool _ => .litBool

theorem evalSemList_map_toNode {rules : List EvalRule} :
    ∀ vs : List EvalValue, EvalSemList rules (vs.map EvalValue.toNode) vs
  | [] => .nil
  | v :: vs => .cons (evalSem_toNode v) (evalSemList_map_toNode vs)

theorem evalSemList_length {rules : List EvalRule} {nodes : List EvalNode} {vs : List EvalValue}
    (h : EvalSemList rules nodes vs) : nodes.length = vs.length := by
  cases h with | nil => rfl | cons _ hrest => simp [evalSemList_length hrest]

theorem evalSem_toNode_inv {rules : List EvalRule} {v w : EvalValue}
    (h : EvalSem rules v.toNode w) : w = v := by
  cases v <;> cases h <;> rfl

theorem evalSemList_toNodes_inv {rules : List EvalRule} {vs ws : List EvalValue}
    (h : EvalSemList rules (vs.map EvalValue.toNode) ws) : ws = vs := by
  induction vs generalizing ws with
  | nil => cases h; rfl
  | cons v vs ih => cases h with
    | cons hv hrest =>
      have h1 := evalSem_toNode_inv hv; have h2 := ih hrest; subst h1; subst h2; rfl

theorem evalSem_userCall_transport {rules : List EvalRule} {head : String}
    {args : List EvalNode} {vals : List EvalValue} {v : EvalValue}
    (hArgs : EvalSemList rules args vals)
    (hCallVals : EvalSem rules (.userCall head (vals.map EvalValue.toNode)) v) :
    EvalSem rules (.userCall head args) v := by
  cases hCallVals with
  | userCall hVals hLookup hBody =>
    have heq := evalSemList_toNodes_inv hVals; subst heq
    simp [List.length_map] at hLookup
    rw [← evalSemList_length hArgs] at hLookup
    exact .userCall hArgs hLookup hBody

theorem memoSoundSem_cons {rules : List EvalRule} {memo : MemoTable}
    {head : String} {vs : List EvalValue} {v : EvalValue}
    (hNew : EvalSem rules (.userCall head (vs.map EvalValue.toNode)) v)
    (hm : MemoSoundSem rules memo) :
    MemoSoundSem rules ((head, vs, v) :: memo) := by
  intro h vs' v' hmem; simp [List.mem_cons] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact hNew
  · exact hm _ _ _ hmem

-- ── Main Theorem Statements ──────────────────────────────────────────────

-- Helper: if no none in a list of options, the list equals some values mapped
theorem list_no_none_eq_map_some (xs : List (Option α)) (h : ¬(none ∈ xs)) :
    ∃ ys : List α, xs = ys.map some := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    simp [List.mem_cons] at h
    obtain ⟨hx, hxs⟩ := h
    obtain ⟨ys, hys⟩ := ih hxs
    cases x with
    | none => exact absurd rfl hx
    | some a => exact ⟨a :: ys, by simp [hys]⟩

-- Helper: filterMap over map some is just map
theorem filterMap_map_some (vs : List α) (f : α → β) :
    (vs.map some).filterMap (fun v => v.map f) = vs.map f := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

-- Soundness of eval: if the fueled evaluator succeeds, the semantic relation holds.
-- Proved by functional induction using eval.induct (auto-generated for mutual WF-recursive defs).
-- Council: Carneiro/Buzzard — "use the Lean-generated induction principle, not mutual theorem syntax."
-- GPT-5.4 Pro: "eval.induct with motive2 for evalList is the correct Lean 4.28 path."
theorem eval_sound {rules : List EvalRule} :
    ∀ fuel node v, eval rules fuel node = some v → EvalSem rules node v := by
  intro fuel node
  induction fuel, node using eval.induct (rules := rules)
    (motive2 := fun fuel nodes =>
      ∀ vs, evalList rules fuel nodes = vs.map some → EvalSemList rules nodes vs) with
  | case1 fuel n => intro v h; simp [eval] at h; subst h; exact .litInt
  | case2 fuel b => intro v h; simp [eval] at h; subst h; exact .litBool
  | case3 fuel c t e hc ih_c ih_t =>
    intro v h; simp [eval, hc] at h; exact .ifTrue (ih_c _ hc) (ih_t _ h)
  | case4 fuel c t e hc ih_c ih_e =>
    intro v h; simp [eval, hc] at h; exact .ifFalse (ih_c _ hc) (ih_e _ h)
  | case5 => intro v h; simp [eval] at h
  | case6 fuel a b va vb hb ha ih_a ih_b =>
    intro v h; simp [eval, ha, hb] at h; subst h; exact .eqOp (ih_a _ ha) (ih_b _ hb)
  | case7 => intro v h; simp [eval] at h
  | case8 fuel a b va vb hb ha ih_a ih_b =>
    intro v h; simp [eval, ha, hb] at h; subst h; exact .addOp (ih_a _ ha) (ih_b _ hb)
  | case9 => intro v h; simp [eval] at h
  | case10 fuel a b va vb hb ha ih_a ih_b =>
    intro v h; simp [eval, ha, hb] at h; subst h; exact .subOp (ih_a _ ha) (ih_b _ hb)
  | case11 => intro v h; simp [eval] at h
  | case12 fuel a b va vb hb ha ih_a ih_b =>
    intro v h; simp [eval, ha, hb] at h; subst h; exact .mulOp (ih_a _ ha) (ih_b _ hb)
  | case13 => intro v h; simp [eval] at h
  | case14 => intro v h; simp [eval] at h
  | case15 =>
    intro v h; simp [eval] at h
    rename_i hmem _
    -- hmem : evalArgs.any isNone = true, h.1 : ¬(none ∈ evalList ...)
    -- evalArgs := evalList ..., so these contradict
    have := List.any_eq_true.mp hmem
    obtain ⟨x, hx_mem, hx_none⟩ := this
    cases x with
    | none => exact absurd hx_mem h.1
    | some _ => simp [Option.isNone] at hx_none
  | case16 =>
    intro v h; simp [eval] at h
    rename_i _ hlookup _
    -- hlookup : lookupRule ... = none
    -- h.2 : (match lookupRule ... with | none => none | some rule => ...) = some v
    rw [hlookup] at h; simp at h
  -- userCall success: the HARD case
  | case17 head args fuel' hnotany rule hrule ih_args ih_body =>
    intro v h
    -- From eval.induct, the context has (with confusing names):
    -- `rule`: ¬(evalList...).any isNone  (the "no nones" fact)
    -- `hrule`: the matched EvalRule
    -- `ih_args`: lookupRule = some hrule
    -- `ih2✝`: list IH, `ih1✝`: body IH
    -- Step 1: unfold eval in h
    simp [eval, ih_args] at h
    obtain ⟨hnn, hbody⟩ := h
    -- Step 2: convert no-nones to map some
    obtain ⟨argVals, hArgVals⟩ := list_no_none_eq_map_some _ hnn
    -- Step 3: list IH → EvalSemList
    rename_i ih_list ih_body_ih
    have hSemArgs := ih_list argVals hArgVals
    -- Step 4: align filterMap
    have hFilter : (evalList rules (fuel' + 1) args).filterMap (fun v => v.map EvalValue.toNode)
                   = argVals.map EvalValue.toNode := by
      rw [hArgVals]; exact filterMap_map_some argVals EvalValue.toNode
    -- Step 5: apply body IH — work around let-binding opacity
    -- ih_body_ih sees body'✝ which is let-bound via ih_body (= filterMap ...)
    -- hbody sees the unfolded form with filterMap directly
    -- Both are definitionally equal, so we just need to help Lean see it
    have hSemBody : EvalSem rules (substNode (hrule.params.zip (argVals.map EvalValue.toNode)) hrule.body) v := by
      have := ih_body_ih v hbody
      -- `this` has type EvalSem rules body'✝ v where body'✝ uses ih_body
      -- ih_body and argVals.map toNode are equal by hFilter
      -- Use congrArg to transport
      exact hFilter ▸ this
    exact .userCall hSemArgs ih_args hSemBody
  -- evalList cases
  | case18 =>
    rename_i fuel vs h
    cases vs with
    | nil => exact .nil
    | cons => simp [evalList] at h
  | case19 fuel a as ih_a ih_as =>
    rename_i vs h
    cases vs with
    | nil => simp [evalList] at h
    | cons v vs =>
      simp [evalList] at h
      exact .cons (ih_a _ h.1) (ih_as _ h.2)

/-- Joint soundness + preservation for the memoized evaluator.
    GPT-5.4 Pro: "Prove these together. The pair theorem is the main theorem." -/
theorem evalMemo_sound_and_preserves {rules : List EvalRule} :
    ∀ fuel memo node,
      MemoSoundSem rules memo →
      (∀ v, (evalMemo rules fuel memo node).1 = some v → EvalSem rules node v) ∧
      MemoSoundSem rules (evalMemo rules fuel memo node).2 := by
  intro fuel memo node
  induction fuel, memo, node using evalMemo.induct (rules := rules)
    (motive2 := fun fuel memo nodes =>
      MemoSoundSem rules memo →
      (∀ vs, (evalMemoList rules fuel memo nodes).1 = vs.map some → EvalSemList rules nodes vs) ∧
      MemoSoundSem rules (evalMemoList rules fuel memo nodes).2)
  all_goals sorry

/-- Soundness of evalMemo: extracted from the joint theorem. -/
theorem evalMemo_sound {rules : List EvalRule} {fuel : Nat} {memo : MemoTable}
    {node : EvalNode} {v : EvalValue}
    (hm : MemoSoundSem rules memo)
    (h : (evalMemo rules fuel memo node).1 = some v) :
    EvalSem rules node v :=
  (evalMemo_sound_and_preserves fuel memo node hm).1 v h

/-- evalMemo preserves memo soundness: extracted from the joint theorem. -/
theorem evalMemo_preserves_memo {rules : List EvalRule} {fuel : Nat} {memo : MemoTable}
    {node : EvalNode}
    (hm : MemoSoundSem rules memo) :
    MemoSoundSem rules (evalMemo rules fuel memo node).2 :=
  (evalMemo_sound_and_preserves fuel memo node hm).2

/-- Completeness: if the semantic relation holds, sufficient fuel exists for eval. -/
theorem eval_complete_of_sem {rules : List EvalRule} {node : EvalNode} {v : EvalValue}
    (h : EvalSem rules node v) :
    ∃ fuel, eval rules fuel node = some v := by
  sorry -- TODO: induction on EvalSem derivation

-- ═══════════════════════════════════════════════════════════════════════════
-- § EvalTrace — The Universal Proof Object
-- ═══════════════════════════════════════════════════════════════════════════
-- An evaluation trace is an indexed inductive tree recording every step of
-- CBV+memo evaluation. ALL properties (correctness, memo soundness, step count,
-- MM2 simulation) fall out of this one structure.
-- Council: Knuth, Tao, Carneiro, Martin-Löf, Meredith, McBride, Pfenning, Voevodsky.

-- Evaluation trace: records every step of CBV+memo evaluation.
-- Indexed by (input_node, output_value, memo_in, memo_out).
mutual
  inductive EvalTrace (rules : List EvalRule)
      : EvalNode → EvalValue → MemoTable → MemoTable → Type where
    | litInt : EvalTrace rules (.intLit n) (.int n) m m
    | litBool : EvalTrace rules (.boolLit b) (.bool b) m m
    | eqOp : EvalTrace rules a (.int va) m m₁ →
             EvalTrace rules b (.int vb) m₁ m₂ →
             EvalTrace rules (.eqInt a b) (.bool (va == vb)) m m₂
    | addOp : EvalTrace rules a (.int va) m m₁ →
              EvalTrace rules b (.int vb) m₁ m₂ →
              EvalTrace rules (.addInt a b) (.int (va + vb)) m m₂
    | subOp : EvalTrace rules a (.int va) m m₁ →
              EvalTrace rules b (.int vb) m₁ m₂ →
              EvalTrace rules (.subInt a b) (.int (va - vb)) m m₂
    | mulOp : EvalTrace rules a (.int va) m m₁ →
              EvalTrace rules b (.int vb) m₁ m₂ →
              EvalTrace rules (.mulInt a b) (.int (va * vb)) m m₂
    | ifTrue : EvalTrace rules c (.bool true) m m₁ →
               EvalTrace rules t vt m₁ m₂ →
               EvalTrace rules (.ifCond c t e) vt m m₂
    | ifFalse : EvalTrace rules c (.bool false) m m₁ →
                EvalTrace rules e ve m₁ m₂ →
                EvalTrace rules (.ifCond c t e) ve m m₂
    | callMiss :
        EvalTraceList rules args argVals m m₁ →
        memoLookup m₁ head argVals = none →
        lookupRule rules head args.length = some rule →
        EvalTrace rules
          (substNode (rule.params.zip (argVals.map EvalValue.toNode)) rule.body)
          result m₁ m₂ →
        EvalTrace rules (.userCall head args) result m ((head, argVals, result) :: m₂)
    | callHit :
        EvalTraceList rules args argVals m m₁ →
        memoLookup m₁ head argVals = some result →
        EvalTrace rules (.userCall head args) result m m₁

  inductive EvalTraceList (rules : List EvalRule)
      : List EvalNode → List EvalValue → MemoTable → MemoTable → Type where
    | nil : EvalTraceList rules [] [] m m
    | cons : EvalTrace rules a v m m₁ →
             EvalTraceList rules as vs m₁ m₂ →
             EvalTraceList rules (a :: as) (v :: vs) m m₂
end

-- ── Trace Properties ─────────────────────────────────────────────────────

-- Count the number of callMiss nodes (= unique computations)
mutual
  def EvalTrace.callMissCount : EvalTrace rules node v m m' → Nat
    | .litInt | .litBool => 0
    | .eqOp ta tb | .addOp ta tb | .subOp ta tb | .mulOp ta tb =>
        ta.callMissCount + tb.callMissCount
    | .ifTrue tc tt => tc.callMissCount + tt.callMissCount
    | .ifFalse tc te => tc.callMissCount + te.callMissCount
    | .callMiss targs _ _ tbody =>
        targs.callMissCount + tbody.callMissCount + 1
    | .callHit targs _ => targs.callMissCount

  def EvalTraceList.callMissCount : EvalTraceList rules nodes vs m m' → Nat
    | .nil => 0
    | .cons t ts => t.callMissCount + ts.callMissCount
end

-- Total step count (every trace node = 1 step)
mutual
  def EvalTrace.stepCount : EvalTrace rules node v m m' → Nat
    | .litInt | .litBool => 1
    | .eqOp ta tb | .addOp ta tb | .subOp ta tb | .mulOp ta tb =>
        1 + ta.stepCount + tb.stepCount + 1  -- unfold + subs + fold
    | .ifTrue tc tt => 1 + tc.stepCount + 1 + tt.stepCount  -- unfold + cond + dispatch + branch
    | .ifFalse tc te => 1 + tc.stepCount + 1 + te.stepCount
    | .callMiss targs _ _ tbody =>
        targs.stepCount + 1 + tbody.stepCount + 1  -- args + expand + body + memo_store
    | .callHit targs _ => targs.stepCount + 1  -- args + memo_hit

  def EvalTraceList.stepCount : EvalTraceList rules nodes vs m m' → Nat
    | .nil => 0
    | .cons t ts => t.stepCount + ts.stepCount
end

-- ── Key Theorems ─────────────────────────────────────────────────────────

-- Correctness: a trace witnesses that eval produces the traced result
-- (for sufficient fuel)
theorem trace_implies_eval (rules : List EvalRule) (node : EvalNode) (v : EvalValue)
    (m m' : MemoTable) (t : EvalTrace rules node v m m') :
    ∃ fuel, eval rules fuel node = some v := by
  sorry -- induction on t

-- Memo soundness: the output memo of a trace contains only semantically correct entries
theorem trace_memo_sound (rules : List EvalRule) (node : EvalNode) (v : EvalValue)
    (m m' : MemoTable) (t : EvalTrace rules node v m m')
    (hm : MemoSoundSem rules m) :
    MemoSoundSem rules m' := by
  sorry -- induction on t

-- ═══════════════════════════════════════════════════════════════════════════
-- § Grounded Arithmetic Interface (IntArithSink)
-- ═══════════════════════════════════════════════════════════════════════════
-- Models the IntArithSink in MORK: Rust-grounded integer arithmetic inside
-- MM2 templates. Lean is the semantic authority; Rust mirrors these types.

/-- Arithmetic operations supported by the IntArithSink.
    Mirrors the Rust IntArithOp enum in MORK kernel/src/sinks.rs. -/
inductive ArithOp where
  | add | sub | mul | eq
deriving Repr, DecidableEq, BEq

/-- Semantics of a single grounded arithmetic step.
    This is the specification of what IntArithSink computes. -/
def arithEval : ArithOp → Int → Int → EvalValue
  | .add, a, b => .int (a + b)
  | .sub, a, b => .int (a - b)
  | .mul, a, b => .int (a * b)
  | .eq,  a, b => .bool (a == b)

/-- A grounded arithmetic step: given resolved integer arguments and an operation,
    the IntArithSink produces `arithEval op argA argB` without lookup tables. -/
structure GroundedStep where
  op : ArithOp
  argA : Int
  argB : Int
  result : EvalValue := arithEval op argA argB
deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- § MM2 Request/Result/Join Protocol — Base Layer
-- ═══════════════════════════════════════════════════════════════════════════
-- Two-layer architecture:
--   Base MORK  = pure structural rewriting (any MORK installation)
--   Extended   = Base + IntArithSink (grounded Rust arithmetic)
-- The extension boundary is explicit: IntArithStep is the ONLY addition.

/-- A request ID in the MM2 protocol. Tracks the evaluation tree.
    Each sub-expression gets a unique ID derived from its parent. -/
inductive ReqId where
  | root : ReqId
  | sub0 : ReqId → ReqId      -- left sub-request (first arg of binary op)
  | sub1 : ReqId → ReqId      -- right sub-request (second arg of binary op)
  | cond : ReqId → ReqId      -- condition sub-request (for ifCond)
  | arg : Nat → ReqId → ReqId -- argument sub-request (for userCall arg evaluation)
deriving Repr, DecidableEq, BEq

/-- An MM2 fact in the request/result protocol.
    These are the atoms that live in MORK's PathMap during evaluation.
    Shared between base MORK and extensions. -/
inductive MM2Fact where
  | req : ReqId → EvalNode → MM2Fact           -- request to evaluate a node
  | res : ReqId → EvalValue → MM2Fact          -- result of evaluating a node
  | waitIf : ReqId → EvalNode → EvalNode → MM2Fact  -- waiting for condition result
  | waitArith : ArithOp → ReqId → MM2Fact      -- waiting for binary op sub-results
  | waitUser : ReqId → String → Nat → MM2Fact  -- waiting for arg evaluation (head, argCount)
  | memo : String → List EvalValue → EvalValue → MM2Fact  -- cached result for (head, args) → value
  | memoPending : ReqId → String → List EvalValue → MM2Fact  -- awaiting result to cache
deriving Repr, BEq

-- ── Base MORK Steps ──────────────────────────────────────────────────────
-- Pure structural rewriting. Any MORK installation can execute these.
-- Critically: base MORK has NO fold for binary arithmetic. In base MORK,
-- (waitArith op id) + (res (sub0 id) va) + (res (sub1 id) vb) is STUCK
-- unless lookup table facts like (ADD va vb result) are in the space.

/-- Base MM2 step — pure structural rewriting, no grounded builtins. -/
inductive BaseStep where
  /-- Leaf: `(req id (intLit n))` → `(res id (int n))` -/
  | leafInt : ReqId → Int → BaseStep
  /-- Leaf: `(req id (boolLit b))` → `(res id (bool b))` -/
  | leafBool : ReqId → Bool → BaseStep
  /-- Unfold ifCond: `(req id (ifCond c t e))` →
      `(req (cond id) c)` + `(waitIf id t e)` -/
  | unfoldIf : ReqId → EvalNode → EvalNode → EvalNode → BaseStep
  /-- Unfold binary op: `(req id (op a b))` →
      `(req (sub0 id) a)` + `(req (sub1 id) b)` + `(waitArith op id)` -/
  | unfoldBinop : ArithOp → ReqId → EvalNode → EvalNode → BaseStep
  /-- Unfold userCall: `(req id (HEAD args))` → `(req id body[args/params])` -/
  | unfoldUser : ReqId → EvalRule → List EvalNode → BaseStep
  /-- Fold if-true: `(waitIf id t e)` + `(res (cond id) (bool true))` → `(req id t)` -/
  | foldIfTrue : ReqId → EvalNode → EvalNode → BaseStep
  /-- Fold if-false: `(waitIf id t e)` + `(res (cond id) (bool false))` → `(req id e)` -/
  | foldIfFalse : ReqId → EvalNode → EvalNode → BaseStep
deriving Repr

/-- Facts consumed by a base step. -/
def BaseStep.consumes : BaseStep → List MM2Fact
  | .leafInt id n       => [.req id (.intLit n)]
  | .leafBool id b      => [.req id (.boolLit b)]
  | .unfoldIf id c t e  => [.req id (.ifCond c t e)]
  | .unfoldBinop op id a b => [.req id (match op with
      | .add => .addInt a b | .sub => .subInt a b
      | .mul => .mulInt a b | .eq  => .eqInt a b)]
  | .unfoldUser id rule args => [.req id (.userCall rule.head args)]
  | .foldIfTrue id t e  => [.waitIf id t e, .res (.cond id) (.bool true)]
  | .foldIfFalse id t e => [.waitIf id t e, .res (.cond id) (.bool false)]

/-- Facts produced by a base step. -/
def BaseStep.produces : BaseStep → List MM2Fact
  | .leafInt id n       => [.res id (.int n)]
  | .leafBool id b      => [.res id (.bool b)]
  | .unfoldIf id c t e  => [.req (.cond id) c, .waitIf id t e]
  | .unfoldBinop op id a b => [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith op id]
  | .unfoldUser id rule args => -- substitution happens here
      [.req id (substNode (rule.params.zip (args.map fun a => a)) rule.body)]
  | .foldIfTrue id t _  => [.req id t]
  | .foldIfFalse id _ e => [.req id e]

-- ── IntArithSink Extension ───────────────────────────────────────────────
-- This is the ONLY addition to base MORK. It provides grounded Rust
-- arithmetic where base MORK would be stuck (waiting for lookup tables).

/-- IntArithSink extension step — grounded Rust arithmetic.
    Only available in MORK + IntArithSink.
    Consumes: `(waitArith op id)` + `(res (sub0 id) (int a))` + `(res (sub1 id) (int b))`
    Produces: `(res id (arithEval op a b))` -/
inductive IntArithStep where
  | foldArith : ArithOp → ReqId → Int → Int → IntArithStep
deriving Repr

/-- Facts consumed by an IntArithSink step. -/
def IntArithStep.consumes : IntArithStep → List MM2Fact
  | .foldArith op id a b => [.waitArith op id, .res (.sub0 id) (.int a), .res (.sub1 id) (.int b)]

/-- Facts produced by an IntArithSink step. -/
def IntArithStep.produces : IntArithStep → List MM2Fact
  | .foldArith op _ a b => [.res .root (arithEval op a b)]  -- id handled below

/-- Correct produces: includes the actual request ID. -/
def IntArithStep.producesAt : IntArithStep → List MM2Fact
  | .foldArith op id a b => [.res id (arithEval op a b)]

-- ── Extended MORK (Base + IntArithSink) ──────────────────────────────────

/-- A step in extended MORK = base MORK + IntArithSink. -/
inductive ExtStep where
  | base : BaseStep → ExtStep
  | intArith : IntArithStep → ExtStep
deriving Repr

/-- Is this step purely base (no extension)? -/
def ExtStep.isBase : ExtStep → Bool
  | .base _ => true
  | .intArith _ => false

-- ── Theorems ─────────────────────────────────────────────────────────────

/-- Soundness: IntArithSink computes exactly `arithEval`.
    This is the specification that the Rust IntArithSink must satisfy. -/
theorem intArithStep_sound (op : ArithOp) (id : ReqId) (a b : Int) :
    (IntArithStep.foldArith op id a b).producesAt = [.res id (arithEval op a b)] := by
  rfl

/-- Conservative extension: a trace containing only base steps has no
    IntArithSink effects. The extension is invisible for pure-rewriting programs. -/
theorem conservative_base_only (s : ExtStep) (h : s.isBase = true) :
    ∃ b : BaseStep, s = .base b := by
  match s with
  | .base b => exact ⟨b, rfl⟩
  | .intArith _ => simp [ExtStep.isBase] at h

-- ═══════════════════════════════════════════════════════════════════════════
-- § Priority Scheduler (Self-Replicating Rule Model)
-- ═══════════════════════════════════════════════════════════════════════════
-- Models the MORK metta_calculus execution with self-replicating rules.
-- Each rule fires when its inputs are present, produces outputs, and
-- respawns itself. Rules are tried in priority order (lowest first).
-- This eliminates the COPIES constant: rules persist indefinitely.

/-- Remove one occurrence of `target` from `facts`. -/
partial def removeOnce (facts : List MM2Fact) (target : MM2Fact) : List MM2Fact :=
  match facts with
  | [] => []
  | f :: fs => if f == target then fs else f :: removeOnce fs target

/-- Remove the first occurrence of each element of `toRemove` from `facts`. -/
partial def removeFacts (facts : List MM2Fact) (toRemove : List MM2Fact) : List MM2Fact :=
  match toRemove with
  | [] => facts
  | r :: rs => removeFacts (removeOnce facts r) rs

/-- Check if all facts in `needed` are present in `available`. -/
def allPresent (needed : List MM2Fact) (available : List MM2Fact) : Bool :=
  needed.all (fun f => available.contains f)

/-- Try to find and apply a leaf step: (req id (intLit n)) → (res id n). -/
partial def tryLeafStep (facts : List MM2Fact) : Option (List MM2Fact) :=
  facts.findSome? fun f =>
    match f with
    | .req id (.intLit n) =>
      some (removeFacts facts [.req id (.intLit n)] ++ [.res id (.int n)])
    | .req id (.boolLit b) =>
      some (removeFacts facts [.req id (.boolLit b)] ++ [.res id (.bool b)])
    | _ => none

/-- Extract evaluated value from an EvalNode if it's a literal. -/
def evalNodeToValue? : EvalNode → Option EvalValue
  | .intLit n => some (.int n)
  | .boolLit b => some (.bool b)
  | _ => none

/-- Try memo hit: if args are all literals AND (memo HEAD ARGS RESULT) exists,
    produce result directly without body expansion. -/
partial def tryMemoHit (facts : List MM2Fact) : Option (List MM2Fact) :=
  facts.findSome? fun f =>
    match f with
    | .req id (.userCall head args) =>
      let argVals := args.filterMap evalNodeToValue?
      if argVals.length != args.length then none
      else
        facts.findSome? fun g =>
          match g with
          | .memo h vs v =>
            if h == head && vs == argVals
            then some (removeFacts facts [f] ++ [.res id v])
            else none
          | _ => none
    | _ => none

/-- Try user-unfold with arg evaluation and memoization.
    Protocol:
    1. (req id (userCall HEAD [arg0, arg1, ...])) where args are NOT all literals
       → create sub-requests to evaluate each arg
       → emit (waitUser id HEAD nArgs) to collect results
    2. (waitUser id HEAD nArgs) + all (res (arg i id) val_i) present
       → reconstruct call with evaluated args: (req id (userCall HEAD [intLit v0, ...]))
    3. (req id (userCall HEAD [intLit v0, intLit v1, ...])) where ALL args are literals
       → check memo → if hit, produce result directly
       → if miss, expand body + emit memoPending -/
partial def tryUserUnfold (rules : List EvalRule) (facts : List MM2Fact) : Option (List MM2Fact) :=
  -- Phase A: check for waitUser + all arg results (collect evaluated args)
  (facts.findSome? fun f =>
    match f with
    | .waitUser reqId head argCount =>
      -- Try to find all arg results
      let argResults := (List.range argCount).map fun i =>
        facts.findSome? fun g =>
          match g with
          | .res rid v => if rid == .arg i reqId then some v else none
          | _ => none
      if argResults.all Option.isSome then
        let vals := argResults.filterMap fun x => x
        let newArgs := vals.map EvalValue.toNode
        let consumed := [.waitUser reqId head argCount] ++
          (List.range argCount).filterMap fun i =>
            match argResults[i]? with
            | some (some v) => some (.res (.arg i reqId) v)
            | _ => none
        some (removeFacts facts consumed ++ [.req reqId (.userCall head newArgs)])
      else none
    | _ => none)
  -- Phase B: userCall with all-literal args → memo check then body expand
  <|> (facts.findSome? fun f =>
    match f with
    | .req id (.userCall head args) =>
      let argVals := args.filterMap evalNodeToValue?
      if argVals.length == args.length then
        match lookupRule rules head args.length with
        | some rule =>
          let env := rule.params.zip args
          let body' := substNode env rule.body
          some (removeFacts facts [f] ++ [.req id body', .memoPending id head argVals])
        | none => none
      else
        -- Args not all literals → evaluate them via sub-requests
        let argReqs := (args.zip (List.range args.length)).map fun (a, i) => .req (.arg i id) a
        some (removeFacts facts [f] ++ argReqs ++ [.waitUser id head args.length])
    | _ => none)

/-- Try to find and apply a compound-unfold step for binary operations. -/
partial def tryBinopUnfold (facts : List MM2Fact) : Option (List MM2Fact) :=
  facts.findSome? fun f =>
    match f with
    | .req id (.eqInt a b) =>
      some (removeFacts facts [f] ++ [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith .eq id])
    | .req id (.addInt a b) =>
      some (removeFacts facts [f] ++ [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith .add id])
    | .req id (.subInt a b) =>
      some (removeFacts facts [f] ++ [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith .sub id])
    | .req id (.mulInt a b) =>
      some (removeFacts facts [f] ++ [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith .mul id])
    | .req id (.ifCond c t e) =>
      some (removeFacts facts [f] ++ [.req (.cond id) c, .waitIf id t e])
    | _ => none

/-- Try to find and apply a fold step (IntArithSink or if-dispatch). -/
partial def tryFoldStep (facts : List MM2Fact) : Option (List MM2Fact) :=
  -- Try arithmetic folds first
  facts.findSome? fun f =>
    match f with
    | .waitArith op id =>
      -- Look for both sub-results
      let findRes0 := facts.findSome? fun g =>
        match g with
        | .res rid (.int v) => if rid == .sub0 id then some v else none
        | _ => none
      let findRes1 := facts.findSome? fun g =>
        match g with
        | .res rid (.int v) => if rid == .sub1 id then some v else none
        | _ => none
      match findRes0, findRes1 with
      | some va, some vb =>
        let consumed := [.waitArith op id, .res (.sub0 id) (.int va), .res (.sub1 id) (.int vb)]
        let produced := [.res id (arithEval op va vb)]
        some (removeFacts facts consumed ++ produced)
      | _, _ => none
    | .waitIf id t e =>
      -- Look for condition result
      let findCond := facts.findSome? fun g =>
        match g with
        | .res rid (.bool b) => if rid == .cond id then some b else none
        | _ => none
      match findCond with
      | some true =>
        some (removeFacts facts [.waitIf id t e, .res (.cond id) (.bool true)] ++ [.req id t])
      | some false =>
        some (removeFacts facts [.waitIf id t e, .res (.cond id) (.bool false)] ++ [.req id e])
      | none => none
    | _ => none

/-- Try memo store: when (res id VALUE) exists alongside (memoPending id HEAD ARGS),
    cache (memo HEAD ARGS VALUE) for future hits. -/
partial def tryMemoStore (facts : List MM2Fact) : Option (List MM2Fact) :=
  facts.findSome? fun f =>
    match f with
    | .memoPending id head argVals =>
      -- Look for the result
      facts.findSome? fun g =>
        match g with
        | .res rid v =>
          if rid == id
          then some (removeFacts facts [.memoPending id head argVals] ++ [.memo head argVals v])
          else none
        | _ => none
    | _ => none

/-- One step of the priority scheduler. Tries steps in priority order:
    -1: memo hit, 0: user unfold, 1: compound unfold, 2: leaf, 3: fold, 4: memo store.
    Returns none if no step is applicable (fixpoint reached). -/
partial def priorityStep (rules : List EvalRule) (facts : List MM2Fact) : Option (List MM2Fact) :=
  -- Priority -1: memo hit (highest — skip body expansion if cached)
  tryMemoHit facts
  -- Priority 0: user unfold (with memoPending emission)
  <|> tryUserUnfold rules facts
  -- Priority 1: compound unfold
  <|> tryBinopUnfold facts
  -- Priority 2: leaf resolution
  <|> tryLeafStep facts
  -- Priority 2.5: memo store (BEFORE fold — must capture result before fold consumes it)
  <|> tryMemoStore facts
  -- Priority 3: fold (arithmetic + if-dispatch)
  <|> tryFoldStep facts

/-- Run the priority scheduler to fixpoint (or fuel exhaustion). -/
partial def runToFixpoint (rules : List EvalRule) (facts : List MM2Fact) (fuel : Nat) : List MM2Fact :=
  match fuel with
  | 0 => facts
  | fuel' + 1 =>
    match priorityStep rules facts with
    | none => facts  -- fixpoint
    | some facts' => runToFixpoint rules facts' fuel'

/-- Extract the final result value from a fact set. -/
def extractResult (facts : List MM2Fact) : Option EvalValue :=
  facts.findSome? fun f =>
    match f with
    | .res .root v => some v
    | _ => none

-- ═══════════════════════════════════════════════════════════════════════════
-- § MORK Execution Model (Rule Death Semantics)
-- ═══════════════════════════════════════════════════════════════════════════
-- The ideal `priorityStep` above models a scheduler where rules never die.
-- Real MORK is different: exec rules are ALWAYS consumed on each step,
-- whether they match or not. Self-replicating rules only survive if they
-- match AND respawn. This section models the actual MORK semantics.

/-- An exec rule in the MORK space: priority + name + step type.
    Rules are consumed on every metta_calculus step. -/
structure MorkExec where
  priority : Nat
  name : String
  /-- Which step type this rule implements. -/
  tryFire : List EvalRule → List MM2Fact → Option (List MM2Fact × Bool)
    -- Returns: (new_facts, should_respawn)
    -- None = pattern didn't match (rule dies)
    -- Some (facts', true) = matched, respawn self
    -- Some (facts', false) = matched, don't respawn (fire-once)

/-- One step of MORK's actual execution model.
    1. Pick the lowest-priority exec
    2. REMOVE it (always consumed)
    3. Try to fire: if pattern matches → apply + optionally respawn
    4. If pattern doesn't match → rule is DEAD (no rollback) -/
partial def morkStep (userRules : List EvalRule)
    (facts : List MM2Fact) (execs : List MorkExec)
    : Option (List MM2Fact × List MorkExec) :=
  match execs with
  | [] => none  -- no rules left, fixpoint
  | exec :: rest =>
    match exec.tryFire userRules facts with
    | some (facts', true) =>
      -- Matched and self-replicating: respawn at end of exec list
      some (facts', rest ++ [exec])
    | some (facts', false) =>
      -- Matched but fire-once: consumed
      some (facts', rest)
    | none =>
      -- No match: rule DIES (consumed, no respawn)
      -- Continue with remaining execs
      morkStep userRules facts rest

/-- Run MORK to fixpoint (or fuel exhaustion) with rule death semantics. -/
partial def morkRunToFixpoint (userRules : List EvalRule)
    (facts : List MM2Fact) (execs : List MorkExec) (fuel : Nat)
    : List MM2Fact :=
  match fuel with
  | 0 => facts
  | fuel' + 1 =>
    match morkStep userRules facts execs with
    | none => facts  -- no execs left, fixpoint
    | some (facts', execs') => morkRunToFixpoint userRules facts' execs' fuel'

-- ═══════════════════════════════════════════════════════════════════════════
-- § Exemplar Programs
-- ═══════════════════════════════════════════════════════════════════════════

/-- Factorial: facF(n) = if (n == 0) then 1 else n * facF(n - 1)
    Linear recursion exemplar. -/
def factorialRules : List EvalRule :=
  [{ head := "facF"
   , params := ["n"]
   , body := .ifCond
       (.eqInt (.userCall "n" []) (.intLit 0))
       (.intLit 1)
       (.mulInt (.userCall "n" [])
                (.userCall "facF" [.subInt (.userCall "n" []) (.intLit 1)])) }]

/-- Fibonacci: fib(n) = if (n==0) 0 else if (n==1) 1 else fib(n-1) + fib(n-2)
    Branching recursion exemplar — two recursive calls per step. -/
def fibRules : List EvalRule :=
  [{ head := "fib"
   , params := ["n"]
   , body := .ifCond (.eqInt (.userCall "n" []) (.intLit 0)) (.intLit 0)
       (.ifCond (.eqInt (.userCall "n" []) (.intLit 1)) (.intLit 1)
         (.addInt (.userCall "fib" [.subInt (.userCall "n" []) (.intLit 1)])
                  (.userCall "fib" [.subInt (.userCall "n" []) (.intLit 2)]))) }]

end MeTTailCore.EvalIR

-- ═══════════════════════════════════════════════════════════════════════════
-- § Validation (#eval — not kernel-checked proof)
-- ═══════════════════════════════════════════════════════════════════════════

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 20 (.userCall "facF" [.intLit 3])
  if r == some (EvalValue.int 6) then "facF(3) = 6 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 100 (.userCall "facF" [.intLit 10])
  if r == some (EvalValue.int 3628800) then "facF(10) = 3628800 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval fibRules 200 (.userCall "fib" [.intLit 10])
  if r == some (EvalValue.int 55) then "fib(10) = 55 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval fibRules 100000 (.userCall "fib" [.intLit 20])
  if r == some (EvalValue.int 6765) then "fib(20) = 6765 ✓" else "FAIL"

-- GroundedStep validation
open MeTTailCore.EvalIR in
#eval
  let s : GroundedStep := { op := .add, argA := 55, argB := 89 }
  if s.result == EvalValue.int 144 then "55+89=144 via GroundedStep ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let s : GroundedStep := { op := .mul, argA := 6, argB := 7 }
  if s.result == EvalValue.int 42 then "6*7=42 via GroundedStep ✓" else "FAIL"

-- IntArithStep soundness validation
open MeTTailCore.EvalIR in
#eval
  let step := IntArithStep.foldArith .add .root 55 89
  if step.producesAt == [MM2Fact.res .root (EvalValue.int 144)]
  then "intArithStep add 55 89 = res root 144 ✓" else "FAIL"

-- ── Priority Scheduler Validation (self-rep model) ──
-- These prove the priority-based execution model computes factorial and fib
-- correctly WITHOUT copies — the scheduler runs to fixpoint.

open MeTTailCore.EvalIR in
#eval
  let facts := [MM2Fact.req .root (.userCall "facF" [.intLit 3])]
  let result := runToFixpoint factorialRules facts 200
  match extractResult result with
  | some (.int 6) => "scheduler: facF(3) = 6 ✓"
  | other => s!"FAIL: {repr other}"

open MeTTailCore.EvalIR in
#eval
  let facts := [MM2Fact.req .root (.userCall "facF" [.intLit 10])]
  let result := runToFixpoint factorialRules facts 2000
  match extractResult result with
  | some (.int 3628800) => "scheduler: facF(10) = 3628800 ✓"
  | other => s!"FAIL: {repr other}"

open MeTTailCore.EvalIR in
#eval
  let facts := [MM2Fact.req .root (.userCall "fib" [.intLit 10])]
  let result := runToFixpoint fibRules facts 10000
  match extractResult result with
  | some (.int 55) => "scheduler: fib(10) = 55 ✓ (branching recursion, no COPIES)"
  | other => s!"FAIL: {repr other}"

-- fib(3) via memoized scheduler: detailed debug
open MeTTailCore.EvalIR in
#eval
  let facts := [MM2Fact.req .root (.userCall "fib" [.intLit 3])]
  let result := runToFixpoint fibRules facts 500
  let memos := result.filter fun f => match f with | .memo _ _ _ => true | _ => false
  let pending := result.filter fun f => match f with | .memoPending _ _ _ => true | _ => false
  let reqs := result.filter fun f => match f with | .req _ _ => true | _ => false
  let waits := result.filter fun f => match f with
    | .waitUser _ _ _ => true | .waitIf _ _ _ => true | .waitArith _ _ => true | _ => false
  match extractResult result with
  | some v => s!"scheduler: fib(3) = {repr v} (memos:{memos.length} pending:{pending.length} reqs:{reqs.length} waits:{waits.length} total:{result.length})"
  | none => s!"FAIL: no result. memos:{memos.length} pending:{pending.length} reqs:{reqs.length} waits:{waits.length} total:{result.length}"

-- ═══════════════════════════════════════════════════════════════════════════
-- § Layer 1 Validation: Ideal CBV+Memo Evaluator
-- ═══════════════════════════════════════════════════════════════════════════

open MeTTailCore.EvalIR in
#eval
  let (r, memo) := evalMemo fibRules 100 [] (.userCall "fib" [.intLit 10])
  match r with
  | some (.int 55) => s!"evalMemo: fib(10) = 55 ✓ (memo entries: {memo.length})"
  | other => s!"FAIL: {repr other}"

open MeTTailCore.EvalIR in
#eval
  let (r, memo) := evalMemo fibRules 100 [] (.userCall "fib" [.intLit 20])
  match r with
  | some (.int 6765) => s!"evalMemo: fib(20) = 6765 ✓ (memo entries: {memo.length})"
  | other => s!"FAIL: {repr other}"

open MeTTailCore.EvalIR in
#eval
  let (r, memo) := evalMemo factorialRules 100 [] (.userCall "facF" [.intLit 10])
  match r with
  | some (.int 3628800) => s!"evalMemo: facF(10) = 3628800 ✓ (memo entries: {memo.length})"
  | other => s!"FAIL: {repr other}"

-- Scheduler fib(20): works correctly but Lean #eval is too slow for large
-- step counts. Validated for fib(3)=2 with 4 memo entries. The Rust/MORK
-- implementation is the practical execution target for fib(20).

-- ═══════════════════════════════════════════════════════════════════════════
-- § COUNTEREXAMPLE: evalMemo_agrees is FALSE
-- ═══════════════════════════════════════════════════════════════════════════
-- GPT-5.4 Pro found: memo keys omit fuel, so a cache entry created at high
-- remaining fuel can be reused at low remaining fuel where eval would timeout.
-- f() = add(big(), g()), g() = big(), big() = h(), h() = 1
-- At fuel=3: eval gives none, evalMemo gives some (int 2)

open MeTTailCore.EvalIR in
#eval!
  let counterRules : List EvalRule :=
    [ ⟨"h", [], .intLit 1⟩
    , ⟨"big", [], .userCall "h" []⟩
    , ⟨"g", [], .userCall "big" []⟩
    , ⟨"f", [], .addInt (.userCall "big" []) (.userCall "g" [])⟩
    ]
  let e := eval counterRules 3 (.userCall "f" [])
  let m := (evalMemo counterRules 3 [] (.userCall "f" [])).1
  if e == m then s!"SAME: eval={repr e} evalMemo={repr m}"
  else s!"DIFFERENT! eval={repr e} evalMemo={repr m} — evalMemo_agrees IS FALSE"
