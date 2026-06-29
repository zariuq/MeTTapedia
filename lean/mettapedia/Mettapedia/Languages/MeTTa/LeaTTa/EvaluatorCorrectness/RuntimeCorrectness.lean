import MettaHyperonFull.Proofs.Results
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-!
# Runtime-correctness boundary lemmas for LeaTTa's minimal interpreter

This module collects small, closed facts that connect the fuelled scheduler to the
certified step layers used by verified-MeTTa examples.  The first boundary is
deliberately narrow: a scheduler item whose top frame is `(eval x)` or
`(evalc x space)` is exactly one call to `evalOp`.

These lemmas keep later proofs from expanding `interpretStack1` while proving the
larger interpreter-correctness theorem.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-! ## Scheduler-to-`evalOp` boundary -/

/-- A non-final top frame `(eval x)` is handled by one direct call to `evalOp`. -/
theorem interpretStack1_eval_eq (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (x : Atom) (b : Bindings) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      evalOp env st prev x b := by
  unfold interpretStack1
  rfl

/-- A non-final top frame `(evalc x space)` is handled by the same `evalOp` call; the
space argument is intentionally ignored by LeaTTa's minimal interpreter at this layer. -/
theorem interpretStack1_evalc_eq (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (x space : Atom) (b : Bindings) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "evalc", x, space] } :: prev, bnd := b } =
      evalOp env st prev x b := by
  unfold interpretStack1
  rfl

/-- Membership form of `interpretStack1_eval_eq`, useful when composing with item
readout lemmas for `evalOp`. -/
theorem mem_interpretStack1_eval_iff (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (x : Atom) (b : Bindings) (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 ↔
      item ∈ (evalOp env st prev x b).1 := by
  rw [interpretStack1_eval_eq]

/-- Membership form of `interpretStack1_evalc_eq`. -/
theorem mem_interpretStack1_evalc_iff (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (x space : Atom) (b : Bindings) (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "evalc", x, space] } :: prev, bnd := b }).1 ↔
      item ∈ (evalOp env st prev x b).1 := by
  rw [interpretStack1_evalc_eq]

/-! ## `evalOp` fall-through to equation lookup -/

/-- If an `evalOp` input instantiates to a symbol-headed expression, grounded dispatch reports
`noReduce`, and the atom is not an embedded minimal operation, then `evalOp` falls through exactly
to `queryOp`.

This is the generic boundary between LeaTTa's grounded-op dispatch layer and the equality-rule query
layer. -/
theorem evalOp_queryOp_of_instantiated_noReduce
    (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    evalOp env st prev x b = queryOp env st prev (Atom.expr (Atom.sym op :: args)) b := by
  unfold evalOp
  simp [hinst, hcall, hembed]

/-- Membership form of `evalOp_queryOp_of_instantiated_noReduce`. -/
theorem mem_evalOp_queryOp_iff_of_instantiated_noReduce
    (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom) (item : Item)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    item ∈ (evalOp env st prev x b).1 ↔
      item ∈ (queryOp env st prev (Atom.expr (Atom.sym op :: args)) b).1 := by
  rw [evalOp_queryOp_of_instantiated_noReduce env st prev x b op args hinst hcall hembed]

/-! ## Scheduler fall-through to equation lookup -/

/-- Direct scheduler-level version of `evalOp_queryOp_of_instantiated_noReduce`. -/
theorem interpretStack1_eval_queryOp_of_instantiated_noReduce
    (env : MinEnv) (fuel : Nat) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      queryOp env st prev (Atom.expr (Atom.sym op :: args)) b := by
  rw [interpretStack1_eval_eq,
    evalOp_queryOp_of_instantiated_noReduce env st prev x b op args hinst hcall hembed]

/-- Membership form of `interpretStack1_eval_queryOp_of_instantiated_noReduce`. -/
theorem mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
    (env : MinEnv) (fuel : Nat) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom) (item : Item)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 ↔
      item ∈ (queryOp env st prev (Atom.expr (Atom.sym op :: args)) b).1 := by
  rw [interpretStack1_eval_queryOp_of_instantiated_noReduce env fuel st prev x b op args hinst
    hcall hembed]

/-- Scheduler-level lift of the generic static-candidate `queryOp` bridge for an `(eval x)` frame.
This is the reusable B1 boundary: `interpretStack1` dispatches through `evalOp` to `queryOp`, and
the selected static candidate contributes the freshened/merged item without unfolding a concrete
program trace. -/
theorem interpretStack1_eval_contains_staticCandidateItem
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x : Atom} {b mb m : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)} {p : Atom × Atom}
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ p :: post)
    (hmatch : mb ∈ matchAtoms (freshenRule (st.counter + pre.length) p.1 p.2).1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false) :
    evalResult prev (instantiate m (freshenRule (st.counter + pre.length) p.1 p.2).2) m ∈
      (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
    (MinEnv.ofAtomsGT atoms gt) fuel st prev x b op args
    (evalResult prev (instantiate m (freshenRule (st.counter + pre.length) p.1 p.2).2) m)
    hinst hcall hembed]
  exact queryOp_contains_instantiated_item_of_staticCandidateSplit
    (MinEnv.ofAtomsGT atoms gt) st prev (Atom.expr (Atom.sym op :: args)) b
    hstatic hNotVarHead hsplit hmatch hmerge hloop

/-- Scheduler-level paired form: an `(eval x)` frame emits the freshened executable item, and the
same static candidate split gives a certified `KernelStep` for the unfreshened matcher witness.

The remaining capstone crossing is to derive `hmatchCore` and relate the two RHS instantiations
from the freshened executable components. -/
theorem interpretStack1_eval_item_and_kernelStep_of_staticCandidateSplit
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {b mb m coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hhead : ∃ k, headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : mb ∈ matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev (instantiate m (freshenRule (st.counter + pre.length) lhs rhs).2) m ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  constructor
  · exact interpretStack1_eval_contains_staticCandidateItem
      (hstatic := hstatic) (hinst := hinst) (hcall := hcall) (hembed := hembed)
      (hNotVarHead := hNotVarHead) (hsplit := hsplit) (hmatch := hmatchFresh)
      (hmerge := hmerge) (hloop := hloop)
  · exact kernelStep_of_staticCandidateSplit_match hhead hsplit hmatchCore

/-- MOPS-facing form of `interpretStack1_eval_item_and_kernelStep_of_staticCandidateSplit`.

This is the canonical B1 scheduler boundary exposed at the certified relation layer: one
symbol-headed `(eval x)` scheduler step emits the executable freshened item, and the same static
candidate/core matcher witness gives the corresponding contextual MOPS step. The theorem keeps the
freshened executable result and the unfreshened certified reduct explicit; closing that equality or
canonicalization gap is a separate caller obligation, not hidden here. -/
theorem interpretStack1_eval_item_and_mopsStep_of_staticCandidateSplit
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {b mb m coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hhead : ∃ k, headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : mb ∈ matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev (instantiate m (freshenRule (st.counter + pre.length) lhs rhs).2) m ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 ∧
      ExprCtxMopsStep atoms (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  rcases interpretStack1_eval_item_and_kernelStep_of_staticCandidateSplit
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := prev)
    (x := x) (lhs := lhs) (rhs := rhs) (b := b) (mb := mb) (m := m)
    (coreB := coreB) (op := op) (args := args) (pre := pre) (post := post)
    hstatic hinst hcall hembed hNotVarHead hhead hsplit hmatchFresh hmerge hloop hmatchCore with
    ⟨hmem, hstep⟩
  exact ⟨hmem, ExprCtxMopsStep.root (kernelStep_iff_mopsStep.mp hstep)⟩

/-- Result-equality form of `interpretStack1_eval_item_and_mopsStep_of_staticCandidateSplit`.

When the executable freshened RHS is proved equal to the certified unfreshened reduct, the actual
scheduler item is already aligned with the contextual MOPS step. This is the B1 shape callers want
after discharging the freshening/canonicalization crux. -/
theorem interpretStack1_eval_item_and_mopsStep_of_staticCandidateSplit_eqResult
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {b mb m coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hhead : ∃ k, headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : mb ∈ matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hresult :
      instantiate m (freshenRule (st.counter + pre.length) lhs rhs).2 =
        instantiate coreB rhs) :
    evalResult prev (instantiate coreB rhs) m ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 ∧
      ExprCtxMopsStep atoms (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hmem :
      evalResult prev (instantiate coreB rhs) m ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
    have hraw := interpretStack1_eval_contains_staticCandidateItem
      (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := prev)
      (x := x) (b := b) (mb := mb) (m := m) (op := op) (args := args)
      (pre := pre) (post := post) (p := (lhs, rhs))
      hstatic hinst hcall hembed hNotVarHead hsplit hmatchFresh hmerge hloop
    simpa [hresult] using hraw
  have hstep :
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) :=
    kernelStep_of_staticCandidateSplit_match hhead hsplit hmatchCore
  exact ⟨hmem, ExprCtxMopsStep.root (kernelStep_iff_mopsStep.mp hstep)⟩

/-- Fully discharged scheduler-level leaf crossing for the identity variable rule `$v ↦ $v` on a
closed symbol-headed redex. This packages the first nontrivial case where runtime freshening,
empty ambient merge, loop pruning, `queryOp`, `interpretStack1`, and the certified `KernelStep`
all line up without an external crossing hypothesis. -/
theorem interpretStack1_eval_var_id_closed
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x : Atom} {op v : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hclosed : (Atom.expr (Atom.sym op :: args)).vars = [])
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.var v, Atom.var v) :: post) :
    evalResult prev (Atom.expr (Atom.sym op :: args))
          [BindingRel.val (counterSuffix (st.counter + pre.length) v)
            (Atom.expr (Atom.sym op :: args))] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (Atom.expr (Atom.sym op :: args)) := by
  have hquery := queryOp_item_and_kernelStep_var_id_closed
    (st := st) (prev := prev) (toEval := Atom.expr (Atom.sym op :: args))
    (target := Atom.expr (Atom.sym op :: args)) (v := v) (pre := pre) (post := post)
    hclosed rfl hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (Atom.expr (Atom.sym op :: args))
        [BindingRel.val (counterSuffix (st.counter + pre.length) v)
          (Atom.expr (Atom.sym op :: args))]) hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-- Scheduler-level variable-free symbolic-rule crossing. This composes the `interpretStack1` /
`evalOp` boundary with the generic `queryOp`/`KernelStep` bridge for symbolic closed rules, while
leaving the ordinary matcher witness as a premise rather than recomputing a concrete rule. -/
theorem interpretStack1_eval_symbolic_rule_closed
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hlhs : SymbolicClosed lhs) (hrhs : SymbolicClosed rhs)
    (hmatch : [] ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post) :
    evalResult prev rhs [] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) rhs := by
  have hquery := queryOp_item_and_kernelStep_symbolic_rule_closed
    (st := st) (prev := prev) (toEval := Atom.expr (Atom.sym op :: args))
    (lhs := lhs) (rhs := rhs) (pre := pre) (post := post)
    hlhs hrhs hmatch hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev rhs []) hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-- Scheduler-level closed-symbolic identity crossing. An `(eval x)` frame whose instantiated redex is
symbol-headed falls through `evalOp`/`queryOp`; for a static candidate `(a, a)` with symbolic closed
`a`, the emitted executable item and the certified `KernelStep` agree.

This is the generic scheduler-level version of
`queryOp_item_and_kernelStep_symbolic_id_closed`; it is intentionally stated over the relation
LeaTTa certifies rather than by simplifying a concrete program trace. -/
theorem interpretStack1_eval_symbolic_id_closed
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hsym : SymbolicClosed (Atom.expr (Atom.sym op :: args)))
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.expr (Atom.sym op :: args), Atom.expr (Atom.sym op :: args)) :: post) :
    evalResult prev (Atom.expr (Atom.sym op :: args)) [] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (Atom.expr (Atom.sym op :: args)) := by
  have hquery := queryOp_item_and_kernelStep_symbolic_id_closed
    (st := st) (prev := prev) (toEval := Atom.expr (Atom.sym op :: args))
    (target := Atom.expr (Atom.sym op :: args)) (pre := pre) (post := post)
    hsym rfl hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (Atom.expr (Atom.sym op :: args)) []) hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-! ## Scheduler crossing for the generic renamed-core binding case -/

/-- Scheduler-level lift of
`queryOp_item_and_kernelStep_of_renamed_closed_coreBinding_reverse`.

This packages the generic B1 bridge at the `interpretStack1` boundary: an `(eval x)` frame whose
instantiated redex is a symbol-headed expression falls through `evalOp`/`queryOp`; the selected
static candidate emits the executable item, and the same candidate/core matcher witness supplies the
certified `KernelStep`.  The statement is deliberately rule-generic and avoids recomputing any
program-specific matcher trace. -/
theorem interpretStack1_eval_renamed_closed_coreBinding_reverse
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t) :
    evalResult prev (instantiate coreB rhs)
          (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hquery := queryOp_item_and_kernelStep_of_renamed_closed_coreBinding_reverse
    (atoms := atoms) (gt := gt) (st := st) (prev := prev)
    (toEval := Atom.expr (Atom.sym op :: args)) (lhs := lhs) (rhs := rhs)
    (coreB := coreB) (pre := pre) (post := post)
    hclosedB hnodup hstatic (by simp [isVariableHeaded]) (by simp [headKey])
    hsplit hmatchFresh hmatchCore hbound
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (instantiate coreB rhs)
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse)
      hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-! ## Scheduler crossing for the no-candidate `NotReducible` case -/

/-- Symbols are unaffected by instantiation under any binding set. -/
theorem instantiate_notReducibleA (b : Bindings) : instantiate b notReducibleA = notReducibleA := by
  simp [notReducibleA, instantiate, Metta.Subst.apply]

/-- Scheduler-level lift of the no-candidate `queryOp` branch: an `(eval x)` frame whose
instantiated redex is symbol-headed, non-grounded, and has no candidates emits `NotReducible`.

This is the constructor-normal-form side of the runtime bridge. It is intentionally generic and
does not compute any particular `interpretFuel` trace. -/
theorem interpretStack1_eval_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hnone : candidatesW env st.world (Atom.expr (Atom.sym op :: args)) = []) :
    finItem prev notReducibleA b ∈
      (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
    env fuel st prev x b op args (finItem prev notReducibleA b) hinst hcall hembed]
  exact queryOp_contains_notReducible_of_no_candidates env st prev _ b hNotVarHead hnone

/-- Exact scheduler form of `interpretStack1_eval_notReducible_of_no_candidates`.
No-candidate symbol-headed evaluation preserves the state and emits a singleton `NotReducible`
item. -/
theorem interpretStack1_eval_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hnone : candidatesW env st.world (Atom.expr (Atom.sym op :: args)) = []) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      ([finItem prev notReducibleA b], st) := by
  rw [interpretStack1_eval_queryOp_of_instantiated_noReduce]
  · exact queryOp_notReducible_of_no_candidates_eq env st prev
      (Atom.expr (Atom.sym op :: args)) b hNotVarHead hnone
  · exact hinst
  · exact hcall
  · exact hembed

/-- Symbol version of `interpretStack1_eval_notReducible_of_no_candidates`. Bare symbols skip
grounded dispatch and go directly to `queryOp`; if no static rule matches, the root evaluator emits
`NotReducible`. -/
theorem interpretStack1_eval_symbol_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String)
    (hinst : instantiate b x = Atom.sym op)
    (hembed : isEmbeddedOp (Atom.sym op) = false)
    (hnone : candidatesW env st.world (Atom.sym op) = []) :
    finItem prev notReducibleA b ∈
      (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_iff]
  unfold evalOp
  simp [hinst, hembed]
  exact queryOp_contains_notReducible_of_no_candidates env st prev (Atom.sym op) b
    (by simp [isVariableHeaded]) hnone

/-- Exact scheduler form for bare-symbol no-candidate evaluation. -/
theorem interpretStack1_eval_symbol_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String)
    (hinst : instantiate b x = Atom.sym op)
    (hembed : isEmbeddedOp (Atom.sym op) = false)
    (hnone : candidatesW env st.world (Atom.sym op) = []) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      ([finItem prev notReducibleA b], st) := by
  rw [interpretStack1_eval_eq]
  unfold evalOp
  simp [hinst, hembed]
  exact queryOp_notReducible_of_no_candidates_eq env st prev (Atom.sym op) b
    (by simp [isVariableHeaded]) hnone

/-! ## One-step harvesting by the fuel driver -/

/-- One fuel-driver step decomposes into one scheduler step, immediate harvesting of final
successors, and recursive processing of the non-final successors followed by the remaining work.

This is the B2 induction surface: later soundness proofs should rewrite by this lemma and apply the
induction hypothesis to the recursive work-list, rather than unfolding concrete execution traces. -/
theorem interpretFuel_cons_step_eq
    (env : MinEnv) (fuel : Nat) (st : St) (it : Item) (rest : List Item)
    (done : List (Atom × Bindings)) :
    interpretFuel env (fuel + 1) st (it :: rest) done =
      let stepped := interpretStack1 env fuel st it
      let results := stepped.1
      let st' := stepped.2
      let finals := (results.filter isFinal).map finalPair
      let more := results.filter (fun r => !isFinal r)
      interpretFuel env fuel st' (more ++ rest) (finals.reverse ++ done) := by
  cases hstep : interpretStack1 env fuel st it with
  | mk results st' =>
      simp [interpretFuel, hstep]

/-- Membership form of `interpretFuel_cons_step_eq` for the recursive work-list. -/
theorem mem_interpretFuel_cons_of_mem_recursive
    (env : MinEnv) (fuel : Nat) (st : St) (it : Item) (rest : List Item)
    (done : List (Atom × Bindings)) (pair : Atom × Bindings)
    (hmem :
      pair ∈
        (let stepped := interpretStack1 env fuel st it
         let results := stepped.1
         let st' := stepped.2
         let finals := (results.filter isFinal).map finalPair
         let more := results.filter (fun r => !isFinal r)
         interpretFuel env fuel st' (more ++ rest) (finals.reverse ++ done)).1) :
    pair ∈ (interpretFuel env (fuel + 1) st (it :: rest) done).1 := by
  rw [interpretFuel_cons_step_eq]
  exact hmem

/-- A final item emitted by the current scheduler step is harvested by the surrounding fuel driver,
even in the presence of remaining work and an existing accumulator. -/
theorem mem_interpretFuel_cons_final_of_mem_interpretStack1
    (env : MinEnv) (fuel : Nat) (st : St) (it out : Item) (rest : List Item)
    (done : List (Atom × Bindings))
    (hmem : out ∈ (interpretStack1 env fuel st it).1)
    (hfinal : isFinal out = true) :
    finalPair out ∈ (interpretFuel env (fuel + 1) st (it :: rest) done).1 := by
  rw [interpretFuel_cons_step_eq]
  cases hstep : interpretStack1 env fuel st it with
  | mk results st' =>
      simp only [hstep] at hmem ⊢
      rw [interpretFuel_done]
      have houtFiltered : out ∈ results.filter isFinal := by
        rw [List.mem_filter]
        exact ⟨hmem, hfinal⟩
      have houtFinals : finalPair out ∈ (results.filter isFinal).map finalPair :=
        List.mem_map.mpr ⟨out, houtFiltered, rfl⟩
      rw [List.reverse_append, List.reverse_reverse, List.append_assoc]
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl houtFinals)))

/-- Non-final scheduler successors are exactly the items that enter the recursive work-list. -/
theorem mem_nonfinal_successors_of_mem_interpretStack1
    (env : MinEnv) (fuel : Nat) (st : St) (it out : Item)
    (hmem : out ∈ (interpretStack1 env fuel st it).1)
    (hnonfinal : isFinal out = false) :
    out ∈ (interpretStack1 env fuel st it).1.filter (fun r => !isFinal r) := by
  rw [List.mem_filter]
  simp [hmem, hnonfinal]

/-! ## Fuel-driver harvest of already-final scheduler outputs -/

/-- `evalResult` opens `(function ...)` results as new work; every other atom is already final. -/
def isFunctionResult : Atom → Bool
  | Atom.expr (Atom.sym "function" :: _) => true
  | _ => false

/-- Non-function results are immediately final readouts under an empty continuation. -/
theorem evalResult_nil_eq_finItem_of_not_function {a : Atom} {b : Bindings}
    (h : isFunctionResult a = false) :
    evalResult [] a b = finItem [] a b := by
  cases a with
  | sym s =>
      simp [evalResult]
  | var v =>
      simp [evalResult]
  | gnd g =>
      simp [evalResult]
  | expr xs =>
      cases xs with
      | nil =>
          simp [evalResult]
      | cons head tail =>
          cases head with
          | sym s =>
              by_cases hs : s = "function"
              · subst hs
                simp [isFunctionResult] at h
              · simp [evalResult, hs]
          | var v =>
              simp [evalResult]
          | gnd g =>
              simp [evalResult]
          | expr ys =>
              simp [evalResult]

/-- Instantiating a variable-free atom leaves it unchanged. This discharges the final-readout
stability side condition in the common closed-result fragment. -/
theorem instantiate_eq_self_of_vars_nil (b : Bindings) :
    ∀ {a : Atom}, a.vars = [] → instantiate b a = a := by
  intro a
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ a
  · intro s _
    simp [instantiate, Metta.Subst.apply]
  · intro v hvars
    simp [Atom.vars] at hvars
  · intro g _
    simp [instantiate, Metta.Subst.apply]
  · intro xs ih hvars
    simp only [instantiate, Metta.Subst.apply]
    congr 1
    rw [← List.map_id xs]
    conv_lhs => rw [List.map_id]
    apply List.map_congr_left
    intro child hchild
    simpa [instantiate] using ih child hchild (by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro v hv
      have hvExpr : v ∈ (Atom.expr xs).vars := by
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hv⟩
      rw [hvars] at hvExpr
      cases hvExpr)

/-- With no query variables to retain, LeaTTa's binding-retention pass drops every binding. This is
the argument-evaluation simplification used by closed programs such as Peano `add`: evaluated
closed arguments cannot leak internal fresh matcher bindings into the surrounding application. -/
theorem restrictBnd_nil_vars (b : Bindings) : restrictBnd [] b = [] := by
  unfold restrictBnd
  change b.filter (fun r => match r with | BindingRel.eq x y => false | _ => false) = []
  apply List.filter_eq_nil_iff.mpr
  intro r _hr
  cases r <;> simp

/-- The public `evalAtomMin` wrapper builds exactly the singleton `(eval a)` frame used by the
fuel-driver bridge lemmas. -/
theorem atomToStack_eval (a : Atom) :
    atomToStack (Atom.expr [Atom.sym "eval", a]) [] =
      [{ atom := Atom.expr [Atom.sym "eval", a] }] := by
  rfl

/-- Fuel-driver harvest of `interpretStack1_eval_symbolic_rule_closed` when the emitted item is
already final.

This is the first B2 composition over an existing B1 crossing: one scheduler-level symbolic rule
step is harvested by the real `interpretFuel` driver and paired with the same certified
`KernelStep`. Function-valued RHS atoms are intentionally excluded by the `heval` premise, because
`evalResult` opens them as non-final work rather than producing a final readout immediately. -/
theorem interpretFuel_eval_symbolic_rule_closed_contains_final
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hlhs : SymbolicClosed lhs) (hrhs : SymbolicClosed rhs)
    (hmatch : [] ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (heval : evalResult [] rhs [] = finItem [] rhs []) :
    (rhs, []) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) rhs := by
  have hstep := interpretStack1_eval_symbolic_rule_closed
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := [])
    (x := x) (lhs := lhs) (rhs := rhs) (op := op) (args := args)
    (pre := pre) (post := post)
    hlhs hrhs hmatch hstatic hinst hcall hembed hsplit
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }
  let out : Item := evalResult [] rhs []
  have hfinal : isFinal out = true := by
    simp [out, heval, finItem, isFinal]
  have hmemFuel :
      finalPair out ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st [it] []).1 :=
    mem_interpretFuel_cons_final_of_mem_interpretStack1
      (MinEnv.ofAtomsGT atoms gt) fuel st it out [] [] (by
        simpa [it, out] using hstep.1) hfinal
  constructor
  · simpa [it, out, heval, finItem, finalPair, Metta.instantiate_nil] using hmemFuel
  · exact hstep.2

/-- Non-function RHS convenience form of
`interpretFuel_eval_symbolic_rule_closed_contains_final`. -/
theorem interpretFuel_eval_symbolic_rule_closed_contains_nonFunction
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hlhs : SymbolicClosed lhs) (hrhs : SymbolicClosed rhs)
    (hmatch : [] ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hnotFunction : isFunctionResult rhs = false) :
    (rhs, []) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) rhs :=
  interpretFuel_eval_symbolic_rule_closed_contains_final
    hlhs hrhs hmatch hstatic hinst hcall hembed hsplit
    (evalResult_nil_eq_finItem_of_not_function hnotFunction)

/-- MOPS-facing form of `interpretFuel_eval_symbolic_rule_closed_contains_nonFunction`. -/
theorem interpretFuel_eval_symbolic_rule_closed_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hlhs : SymbolicClosed lhs) (hrhs : SymbolicClosed rhs)
    (hmatch : [] ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hnotFunction : isFunctionResult rhs = false) :
    (rhs, []) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) rhs := by
  rcases interpretFuel_eval_symbolic_rule_closed_contains_nonFunction
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (op := op) (args := args) (pre := pre) (post := post)
    hlhs hrhs hmatch hstatic hinst hcall hembed hsplit hnotFunction with
    ⟨hmem, hstep⟩
  exact ⟨hmem,
    exprCtxKernelChain_to_mops
      (kernelChain_to_exprCtxKernelChain
        (Relation.ReflTransGen.single hstep))⟩

/-- Public minimal-evaluator form of
`interpretFuel_eval_symbolic_rule_closed_contains_mops`. -/
theorem evalAtomMin_symbolic_rule_closed_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {fuel : Nat}
    {x lhs rhs : Atom} {op : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hlhs : SymbolicClosed lhs) (hrhs : SymbolicClosed rhs)
    (hmatch : [] ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hnotFunction : isFunctionResult rhs = false) :
    rhs ∈ evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) rhs := by
  rcases interpretFuel_eval_symbolic_rule_closed_contains_mops
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (op := op) (args := args) (pre := pre) (post := post)
    hlhs hrhs hmatch rfl hinst hcall hembed hsplit hnotFunction with
    ⟨hmem, hreach⟩
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr ⟨(rhs, []), by simpa [atomToStack_eval] using hmem, rfl⟩
  · exact hreach

/-- Fuel-driver harvest of the equality-shaped static-candidate B1 crossing.

If the executable freshened RHS has already been proved equal to the certified unfreshened reduct,
and that reduct is stable under the harvested bindings, one real `interpretFuel` step returns the
certified reduct while exposing the same contextual MOPS step. -/
theorem interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {mb m coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hhead : ∃ k, headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : mb ∈ matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge [] mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hresult :
      instantiate m (freshenRule (st.counter + pre.length) lhs rhs).2 =
        instantiate coreB rhs)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false)
    (hstable : instantiate m (instantiate coreB rhs) = instantiate coreB rhs) :
    (instantiate coreB rhs, m) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      ExprCtxMopsStep atoms (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hstep := interpretStack1_eval_item_and_mopsStep_of_staticCandidateSplit_eqResult
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := [])
    (x := x) (lhs := lhs) (rhs := rhs) (b := []) (mb := mb) (m := m)
    (coreB := coreB) (op := op) (args := args) (pre := pre) (post := post)
    hstatic hinst hcall hembed hNotVarHead hhead hsplit hmatchFresh hmerge hloop
    hmatchCore hresult
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }
  let out : Item := evalResult [] (instantiate coreB rhs) m
  have heval : out = finItem [] (instantiate coreB rhs) m := by
    simpa [out] using
      (evalResult_nil_eq_finItem_of_not_function
        (a := instantiate coreB rhs) (b := m) hnotFunction)
  have hfinal : isFinal out = true := by
    simp [out, heval, finItem, isFinal]
  have hmemFuel :
      finalPair out ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st [it] []).1 :=
    mem_interpretFuel_cons_final_of_mem_interpretStack1
      (MinEnv.ofAtomsGT atoms gt) fuel st it out [] [] (by
        simpa [it, out] using hstep.1) hfinal
  constructor
  · simpa [it, out, heval, finItem, finalPair, hstable] using hmemFuel
  · exact hstep.2

/-- Fuel-driver harvest of the generic renamed-core binding crossing when the emitted RHS is
already final.

This is the first B2 theorem that composes the generic B1 crossing all the way through a real
`interpretFuel` readout: the scheduler emits a final item, the fuel driver harvests it, and the
certified root step is returned as a `ReflTransGen KernelStep` chain. The `hstable` premise is the
ordinary final-readout stability condition: applying the harvested bindings to the already
instantiated RHS does not change it. Closed RHS results discharge it by a separate closedness lemma
at use sites. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_final
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false)
    (hstable :
      instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (instantiate coreB rhs) =
        instantiate coreB rhs) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep atoms gt)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  let m := (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
  have hstep := interpretStack1_eval_renamed_closed_coreBinding_reverse
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := [])
    (x := x) (lhs := lhs) (rhs := rhs) (coreB := coreB)
    (op := op) (args := args) (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hmatchFresh hmatchCore hbound
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }
  let out : Item := evalResult [] (instantiate coreB rhs) m
  have heval : out = finItem [] (instantiate coreB rhs) m := by
    simpa [out, m] using
      (evalResult_nil_eq_finItem_of_not_function
        (a := instantiate coreB rhs) (b := m) hnotFunction)
  have hfinal : isFinal out = true := by
    simp [out, heval, finItem, isFinal]
  have hmemFuel :
      finalPair out ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st [it] []).1 :=
    mem_interpretFuel_cons_final_of_mem_interpretStack1
      (MinEnv.ofAtomsGT atoms gt) fuel st it out [] [] (by
        simpa [it, out, m] using hstep.1) hfinal
  constructor
  · simpa [it, out, heval, finItem, finalPair, m, hstable] using hmemFuel
  · exact Relation.ReflTransGen.single hstep.2

/-- Closed-result convenience form of
`interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_final`. Variable-free certified
reducts are stable under the final readout's harvested bindings, so no separate stability premise is
needed. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep atoms gt)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) :=
  interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_final
    hclosedB hnodup hstatic hinst hcall hembed hsplit hmatchFresh hmatchCore hbound
    hnotFunction (instantiate_eq_self_of_vars_nil _ hclosedResult)

/-- MOPS-facing closed-result form of
`interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed`. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hmatchFresh hmatchCore hbound
    hclosedResult hnotFunction with
    ⟨hmem, hreach⟩
  exact ⟨hmem,
    exprCtxKernelChain_to_mops (kernelChain_to_exprCtxKernelChain hreach)⟩

/-- Public minimal-evaluator form of
`interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops`. -/
theorem evalAtomMin_renamed_closed_coreBinding_reverse_contains_closed_mops
    {atoms : List Atom} {gt : GroundingTable} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchFresh : renameBindings (counterSuffix (St.init.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (St.init.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    instantiate coreB rhs ∈ evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup rfl hinst hcall hembed hsplit hmatchFresh hmatchCore hbound
    hclosedResult hnotFunction with
    ⟨hmem, hreach⟩
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr
      ⟨(instantiate coreB rhs,
          (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse),
        by simpa [atomToStack_eval] using hmem, rfl⟩
  · exact hreach

/-- Abstract B2 soundness induction for the fuel driver.

To prove a concrete `interpretFuel` soundness theorem, instantiate `I` with the invariant carried by
each pending work item, and instantiate `P` with the desired property of harvested result pairs. The
two step hypotheses are exactly the obligations supplied by the one-step bridge: final scheduler
successors produce sound readouts, and non-final scheduler successors preserve the work invariant.

The `hExhausted` premise is intentionally explicit. Fuel exhaustion is observable as
`StackOverflow`, so any theorem that wants only genuine kernel reductions must either assume
adequate fuel or prove the overflow case impossible. -/
theorem interpretFuel_sound_by_invariant
    (env : MinEnv) (P : Atom × Bindings → Prop) (I : Item → Prop)
    (hFinalStep :
      ∀ fuel st it out,
        I it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out))
    (hNonfinalStep :
      ∀ fuel st it out,
        I it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → I out)
    (hExhausted : ∀ it, I it → P (if isFinal it then finalPair it else exhaustedPair it)) :
    ∀ fuel st work done,
      (∀ p ∈ done, P p) →
        (∀ it ∈ work, I it) →
          ∀ p ∈ (interpretFuel env fuel st work done).1, P p := by
  intro fuel
  induction fuel with
  | zero =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp hp with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          cases hstep : interpretStack1 env fuel st it with
          | mk results st' =>
              simp only [interpretFuel, hstep] at hp
              have hIt : I it := hwork it (by simp)
              have hdone' :
                  ∀ p ∈ ((results.filter isFinal).map finalPair).reverse ++ done, P p := by
                intro q hq
                rcases List.mem_append.mp hq with hFinalsRev | hDone
                · have hFinals : q ∈ (results.filter isFinal).map finalPair :=
                    List.mem_reverse.mp hFinalsRev
                  rcases List.mem_map.mp hFinals with ⟨out, houtFiltered, rfl⟩
                  have houtParts := List.mem_filter.mp houtFiltered
                  exact hFinalStep fuel st it out hIt
                    (by simpa [hstep] using houtParts.1) houtParts.2
                · exact hdone q hDone
              have hwork' :
                  ∀ out ∈ results.filter (fun r => !isFinal r) ++ rest, I out := by
                intro out hout
                rcases List.mem_append.mp hout with hMore | hRest
                · have houtParts := List.mem_filter.mp hMore
                  have hnonfinal : isFinal out = false := by
                    cases hfin : isFinal out <;> simp [hfin] at houtParts ⊢
                  exact hNonfinalStep fuel st it out hIt
                    (by simpa [hstep] using houtParts.1) hnonfinal
                · exact hwork out (by simp [hRest])
              exact ih st' (results.filter (fun r => !isFinal r) ++ rest)
                (((results.filter isFinal).map finalPair).reverse ++ done)
                hdone' hwork' p hp

/-- State-aware B2 soundness induction for the fuel driver.

This is the version needed for the full runtime-correctness capstone: `interpretFuel` threads a
state through the work-list, so the pending-item invariant may depend on the current state. The
extra `hCarryRest` premise records the precise obligation for old work when the current scheduler
step advances the state. In the static equation-rule fragment this premise is usually discharged by
showing the invariant is insensitive to the counter/world fields changed by the preceding step. -/
theorem interpretFuel_sound_by_state_invariant
    (env : MinEnv) (P : Atom × Bindings → Prop) (I : St → Item → Prop)
    (hFinalStep :
      ∀ fuel st it out,
        I st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out))
    (hNonfinalStep :
      ∀ fuel st it out,
        I st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → I (interpretStack1 env fuel st it).2 out)
    (hCarryRest :
      ∀ fuel st it restItem,
        I st it → I st restItem → I (interpretStack1 env fuel st it).2 restItem)
    (hExhausted : ∀ st it, I st it → P (if isFinal it then finalPair it else exhaustedPair it)) :
    ∀ fuel st work done,
      (∀ p ∈ done, P p) →
        (∀ it ∈ work, I st it) →
          ∀ p ∈ (interpretFuel env fuel st work done).1, P p := by
  intro fuel
  induction fuel with
  | zero =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp hp with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted st it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          cases hstep : interpretStack1 env fuel st it with
          | mk results st' =>
              simp only [interpretFuel, hstep] at hp
              have hIt : I st it := hwork it (by simp)
              have hdone' :
                  ∀ p ∈ ((results.filter isFinal).map finalPair).reverse ++ done, P p := by
                intro q hq
                rcases List.mem_append.mp hq with hFinalsRev | hDone
                · have hFinals : q ∈ (results.filter isFinal).map finalPair :=
                    List.mem_reverse.mp hFinalsRev
                  rcases List.mem_map.mp hFinals with ⟨out, houtFiltered, rfl⟩
                  have houtParts := List.mem_filter.mp houtFiltered
                  exact hFinalStep fuel st it out hIt
                    (by simpa [hstep] using houtParts.1) houtParts.2
                · exact hdone q hDone
              have hwork' :
                  ∀ out ∈ results.filter (fun r => !isFinal r) ++ rest, I st' out := by
                intro out hout
                rcases List.mem_append.mp hout with hMore | hRest
                · have houtParts := List.mem_filter.mp hMore
                  have hnonfinal : isFinal out = false := by
                    cases hfin : isFinal out <;> simp [hfin] at houtParts ⊢
                  simpa [hstep] using
                    hNonfinalStep fuel st it out hIt
                      (by simpa [hstep] using houtParts.1) hnonfinal
                · have hRestI : I st out := hwork out (by simp [hRest])
                  simpa [hstep] using hCarryRest fuel st it out hIt hRestI
              exact ih st' (results.filter (fun r => !isFinal r) ++ rest)
                (((results.filter isFinal).map finalPair).reverse ++ done)
                hdone' hwork' p hp

/-- Singleton-work, empty-accumulator form of `interpretFuel_sound_by_state_invariant`, matching the
shape used by `mettaEval` when it invokes the minimal interpreter on `(eval w)`. -/
theorem interpretFuel_singleton_sound_by_state_invariant
    (env : MinEnv) (P : Atom × Bindings → Prop) (I : St → Item → Prop)
    (hFinalStep :
      ∀ fuel st it out,
        I st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out))
    (hNonfinalStep :
      ∀ fuel st it out,
        I st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → I (interpretStack1 env fuel st it).2 out)
    (hCarryRest :
      ∀ fuel st it restItem,
        I st it → I st restItem → I (interpretStack1 env fuel st it).2 restItem)
    (hExhausted : ∀ st it, I st it → P (if isFinal it then finalPair it else exhaustedPair it))
    {fuel : Nat} {st : St} {it : Item}
    (hit : I st it) :
    ∀ p ∈ (interpretFuel env fuel st [it] []).1, P p :=
  interpretFuel_sound_by_state_invariant env P I hFinalStep hNonfinalStep hCarryRest hExhausted
    fuel st [it] [] (by intro p hp; cases hp)
    (by
      intro it' hit'
      cases hit' with
      | head => simpa using hit
      | tail _ htail => cases htail)

/-- Fuel-aware B2 soundness induction for the fuel driver.

This is the capstone-ready form. The invariant may mention the remaining fuel, so adequate-fuel
arguments can rule out `StackOverflow` rather than treating exhaustion as a normal semantic result.
In the recursive branch, scheduler successors and the old tail are both checked at the decremented
fuel, exactly matching `interpretFuel`'s recursive call. -/
theorem interpretFuel_sound_by_fuel_state_invariant
    (env : MinEnv) (P : Atom × Bindings → Prop) (I : Nat → St → Item → Prop)
    (hFinalStep :
      ∀ fuel st it out,
        I (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out))
    (hNonfinalStep :
      ∀ fuel st it out,
        I (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → I fuel (interpretStack1 env fuel st it).2 out)
    (hCarryRest :
      ∀ fuel st it restItem,
        I (fuel + 1) st it → I (fuel + 1) st restItem →
          I fuel (interpretStack1 env fuel st it).2 restItem)
    (hExhausted : ∀ st it, I 0 st it → P (if isFinal it then finalPair it else exhaustedPair it)) :
    ∀ fuel st work done,
      (∀ p ∈ done, P p) →
        (∀ it ∈ work, I fuel st it) →
          ∀ p ∈ (interpretFuel env fuel st work done).1, P p := by
  intro fuel
  induction fuel with
  | zero =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp hp with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted st it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp hp)
      | cons it rest =>
          cases hstep : interpretStack1 env fuel st it with
          | mk results st' =>
              simp only [interpretFuel, hstep] at hp
              have hIt : I (fuel + 1) st it := hwork it (by simp)
              have hdone' :
                  ∀ p ∈ ((results.filter isFinal).map finalPair).reverse ++ done, P p := by
                intro q hq
                rcases List.mem_append.mp hq with hFinalsRev | hDone
                · have hFinals : q ∈ (results.filter isFinal).map finalPair :=
                    List.mem_reverse.mp hFinalsRev
                  rcases List.mem_map.mp hFinals with ⟨out, houtFiltered, rfl⟩
                  have houtParts := List.mem_filter.mp houtFiltered
                  exact hFinalStep fuel st it out hIt
                    (by simpa [hstep] using houtParts.1) houtParts.2
                · exact hdone q hDone
              have hwork' :
                  ∀ out ∈ results.filter (fun r => !isFinal r) ++ rest, I fuel st' out := by
                intro out hout
                rcases List.mem_append.mp hout with hMore | hRest
                · have houtParts := List.mem_filter.mp hMore
                  have hnonfinal : isFinal out = false := by
                    cases hfin : isFinal out <;> simp [hfin] at houtParts ⊢
                  simpa [hstep] using
                    hNonfinalStep fuel st it out hIt
                      (by simpa [hstep] using houtParts.1) hnonfinal
                · have hRestI : I (fuel + 1) st out := hwork out (by simp [hRest])
                  simpa [hstep] using hCarryRest fuel st it out hIt hRestI
              exact ih st' (results.filter (fun r => !isFinal r) ++ rest)
                (((results.filter isFinal).map finalPair).reverse ++ done)
                hdone' hwork' p hp

/-- Singleton-work, empty-accumulator form of the fuel-aware B2 induction. This is the direct
shape for `mettaEval`'s minimal-interpreter call. -/
theorem interpretFuel_singleton_sound_by_fuel_state_invariant
    (env : MinEnv) (P : Atom × Bindings → Prop) (I : Nat → St → Item → Prop)
    (hFinalStep :
      ∀ fuel st it out,
        I (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out))
    (hNonfinalStep :
      ∀ fuel st it out,
        I (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → I fuel (interpretStack1 env fuel st it).2 out)
    (hCarryRest :
      ∀ fuel st it restItem,
        I (fuel + 1) st it → I (fuel + 1) st restItem →
          I fuel (interpretStack1 env fuel st it).2 restItem)
    (hExhausted : ∀ st it, I 0 st it → P (if isFinal it then finalPair it else exhaustedPair it))
    {fuel : Nat} {st : St} {it : Item}
    (hit : I fuel st it) :
    ∀ p ∈ (interpretFuel env fuel st [it] []).1, P p :=
  interpretFuel_sound_by_fuel_state_invariant env P I hFinalStep hNonfinalStep hCarryRest
    hExhausted fuel st [it] [] (by intro p hp; cases hp)
    (by
      intro it' hit'
      cases hit' with
      | head => simpa using hit
      | tail _ htail => cases htail)

/-! ## Fuel-driver soundness as reachability lifting -/

/-- Reachability-aware B2 induction for the fuel driver.

This is the theorem that turns a one-step scheduler bridge into a multi-step semantic bridge.  The
invariant `I fuel st it cur` says that pending work item `it` is currently responsible for semantic
atom `cur`; the theorem threads the additional fact that `cur` is reachable from the original root.

The final-step premise contributes a semantic chain from the current atom to the harvested readout.
The non-final premise contributes a semantic chain from the current atom to the next pending item's
current atom.  The proof composes those local chains through `Relation.ReflTransGen.trans` while the
existing fuel/work-list induction handles the scheduler accumulator bookkeeping. -/
theorem interpretFuel_sound_by_reachable_fuel_state_invariant
    (env : MinEnv) (R : Atom → Atom → Prop) (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → Relation.ReflTransGen R cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen R cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen R cur (if isFinal it then finalPair it else exhaustedPair it).1) :
    ∀ fuel st work done root,
      (∀ p ∈ done, Relation.ReflTransGen R root p.1) →
        (∀ it ∈ work, ∃ cur, Relation.ReflTransGen R root cur ∧ I fuel st it cur) →
          ∀ p ∈ (interpretFuel env fuel st work done).1,
            Relation.ReflTransGen R root p.1 := by
  intro fuel st work done root hdone hwork p hp
  let P : Atom × Bindings → Prop := fun p => Relation.ReflTransGen R root p.1
  let J : Nat → St → Item → Prop := fun fuel st it =>
    ∃ cur, Relation.ReflTransGen R root cur ∧ I fuel st it cur
  have hFinalJ :
      ∀ fuel st it out,
        J (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → P (finalPair out) := by
    intro fuel st it out hJ hout hfinal
    rcases hJ with ⟨cur, hroot, hI⟩
    exact hroot.trans (hFinalStep fuel st it cur out hI hout hfinal)
  have hNonfinalJ :
      ∀ fuel st it out,
        J (fuel + 1) st it →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false → J fuel (interpretStack1 env fuel st it).2 out := by
    intro fuel st it out hJ hout hnonfinal
    rcases hJ with ⟨cur, hroot, hI⟩
    rcases hNonfinalStep fuel st it cur out hI hout hnonfinal with ⟨cur', hcur, hI'⟩
    exact ⟨cur', hroot.trans hcur, hI'⟩
  have hCarryRestJ :
      ∀ fuel st it restItem,
        J (fuel + 1) st it → J (fuel + 1) st restItem →
          J fuel (interpretStack1 env fuel st it).2 restItem := by
    intro fuel st it restItem hJ hRest
    rcases hJ with ⟨cur, _hrootCur, hI⟩
    rcases hRest with ⟨restCur, hrootRest, hRestI⟩
    exact ⟨restCur, hrootRest, hCarryRest fuel st it cur restItem restCur hI hRestI⟩
  have hExhaustedJ :
      ∀ st it, J 0 st it → P (if isFinal it then finalPair it else exhaustedPair it) := by
    intro st it hJ
    rcases hJ with ⟨cur, hroot, hI⟩
    exact hroot.trans (hExhausted st it cur hI)
  exact interpretFuel_sound_by_fuel_state_invariant env P J
    hFinalJ hNonfinalJ hCarryRestJ hExhaustedJ fuel st work done hdone hwork p hp

/-- Singleton-work, empty-accumulator form of
`interpretFuel_sound_by_reachable_fuel_state_invariant`. This is the shape used by an
`interpretFuel` call created from one initial evaluator frame. -/
theorem interpretFuel_singleton_sound_by_reachable_fuel_state_invariant
    (env : MinEnv) (R : Atom → Atom → Prop) (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → Relation.ReflTransGen R cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen R cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen R cur (if isFinal it then finalPair it else exhaustedPair it).1)
    {fuel : Nat} {st : St} {it : Item} {root cur : Atom}
    (hroot : Relation.ReflTransGen R root cur)
    (hit : I fuel st it cur) :
    ∀ p ∈ (interpretFuel env fuel st [it] []).1, Relation.ReflTransGen R root p.1 :=
  interpretFuel_sound_by_reachable_fuel_state_invariant env R I hFinalStep hNonfinalStep
    hCarryRest hExhausted fuel st [it] [] root (by intro p hp; cases hp)
    (by
      intro it' hit'
      cases hit' with
      | head => exact ⟨cur, hroot, hit⟩
      | tail _ htail => cases htail)

/-- `evalAtomMin` form of `interpretFuel_singleton_sound_by_reachable_fuel_state_invariant`.

`evalAtomMin` is just the public minimal-evaluator wrapper around a singleton `(eval atom)` work
item, with bindings projected away. This lemma keeps later proofs at the fuel-driver invariant
level while still stating their readout premise against the executable wrapper. -/
theorem evalAtomMin_sound_by_reachable_fuel_state_invariant
    (env : MinEnv) (R : Atom → Atom → Prop) (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true → Relation.ReflTransGen R cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen R cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen R cur (if isFinal it then finalPair it else exhaustedPair it).1)
    {fuel : Nat} {atom root cur out : Atom}
    (hroot : Relation.ReflTransGen R root cur)
    (hit : I fuel St.init
      { stack := atomToStack (Atom.expr [Atom.sym "eval", atom]) [], bnd := [] } cur)
    (hout : out ∈ evalAtomMin env fuel atom) :
    Relation.ReflTransGen R root out := by
  unfold evalAtomMin interpretAtom at hout
  rcases List.mem_map.mp hout with ⟨p, hp, hpout⟩
  have hpair :=
    interpretFuel_singleton_sound_by_reachable_fuel_state_invariant
      env R I hFinalStep hNonfinalStep hCarryRest hExhausted hroot hit p hp
  simpa [hpout] using hpair

/-- MOPS-facing wrapper for `interpretFuel_sound_by_reachable_fuel_state_invariant`.

This is the generic B3 composition at the fuel-driver level: once a caller has proved the B2
premises against contextual `KernelStep`, every harvested fuel-driver readout is exported as
contextual MOPS reachability. -/
theorem interpretFuel_sound_by_reachable_kernel_to_mops
    (env : MinEnv) (rules : List Atom) (gt : GroundingTable)
    (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true →
              Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur
            (if isFinal it then finalPair it else exhaustedPair it).1) :
    ∀ fuel st work done root,
      (∀ p ∈ done, Relation.ReflTransGen (ExprCtxKernelStep rules gt) root p.1) →
        (∀ it ∈ work,
          ∃ cur, Relation.ReflTransGen (ExprCtxKernelStep rules gt) root cur ∧
            I fuel st it cur) →
          ∀ p ∈ (interpretFuel env fuel st work done).1,
            Relation.ReflTransGen (ExprCtxMopsStep rules) root p.1 := by
  intro fuel st work done root hdone hwork p hp
  exact exprCtxKernelChain_to_mops
    (interpretFuel_sound_by_reachable_fuel_state_invariant
      env (ExprCtxKernelStep rules gt) I hFinalStep hNonfinalStep hCarryRest hExhausted
      fuel st work done root hdone hwork p hp)

/-- Singleton-work, empty-accumulator form of
`interpretFuel_sound_by_reachable_kernel_to_mops`. -/
theorem interpretFuel_singleton_sound_by_reachable_kernel_to_mops
    (env : MinEnv) (rules : List Atom) (gt : GroundingTable)
    (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true →
              Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur
            (if isFinal it then finalPair it else exhaustedPair it).1)
    {fuel : Nat} {st : St} {it : Item} {root cur : Atom}
    (hroot : Relation.ReflTransGen (ExprCtxKernelStep rules gt) root cur)
    (hit : I fuel st it cur) :
    ∀ p ∈ (interpretFuel env fuel st [it] []).1,
      Relation.ReflTransGen (ExprCtxMopsStep rules) root p.1 := by
  refine interpretFuel_sound_by_reachable_kernel_to_mops
    env rules gt I hFinalStep hNonfinalStep hCarryRest hExhausted
    fuel st [it] [] root ?_ ?_
  · intro p hp
    cases hp
  · intro it' hit'
    cases hit' with
    | head => exact ⟨cur, hroot, hit⟩
    | tail _ htail => cases htail

/-- MOPS-facing wrapper for `evalAtomMin_sound_by_reachable_fuel_state_invariant`.

Callers may prove their one-step scheduler obligations against the contextual `KernelStep`
relation, then export the executable readout as contextual MOPS reachability using LeaTTa's
certified `KernelStep ↔ MopsStep` correspondence. -/
theorem evalAtomMin_sound_by_reachable_kernel_to_mops
    (env : MinEnv) (rules : List Atom) (gt : GroundingTable)
    (I : Nat → St → Item → Atom → Prop)
    (hFinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = true →
              Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur (finalPair out).1)
    (hNonfinalStep :
      ∀ fuel st it cur out,
        I (fuel + 1) st it cur →
          out ∈ (interpretStack1 env fuel st it).1 →
            isFinal out = false →
              ∃ cur', Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur cur' ∧
                I fuel (interpretStack1 env fuel st it).2 out cur')
    (hCarryRest :
      ∀ fuel st it cur restItem restCur,
        I (fuel + 1) st it cur → I (fuel + 1) st restItem restCur →
          I fuel (interpretStack1 env fuel st it).2 restItem restCur)
    (hExhausted :
      ∀ st it cur,
        I 0 st it cur →
          Relation.ReflTransGen (ExprCtxKernelStep rules gt) cur
            (if isFinal it then finalPair it else exhaustedPair it).1)
    {fuel : Nat} {atom root cur out : Atom}
    (hroot : Relation.ReflTransGen (ExprCtxKernelStep rules gt) root cur)
    (hit : I fuel St.init
      { stack := atomToStack (Atom.expr [Atom.sym "eval", atom]) [], bnd := [] } cur)
    (hout : out ∈ evalAtomMin env fuel atom) :
    Relation.ReflTransGen (ExprCtxMopsStep rules) root out := by
  unfold evalAtomMin interpretAtom at hout
  rcases List.mem_map.mp hout with ⟨p, hp, hpout⟩
  have hpair :=
    interpretFuel_singleton_sound_by_reachable_kernel_to_mops
      env rules gt I hFinalStep hNonfinalStep hCarryRest hExhausted hroot hit p hp
  simpa [hpout] using hpair

/-- An already-final item is returned unchanged by one scheduler step. -/
theorem interpretStack1_final_eq (env : MinEnv) (fuel : Nat) (st : St) (it : Item)
    (hfinal : isFinal it = true) :
    interpretStack1 env fuel st it = ([it], st) := by
  cases it with
  | mk stack bnd =>
      cases stack with
      | nil => simp [isFinal] at hfinal
      | cons top rest =>
          cases rest with
          | nil =>
              cases top
              simp [isFinal] at hfinal
              unfold interpretStack1
              simp [hfinal]
          | cons _ _ => simp [isFinal] at hfinal

/-- If a single scheduler step emits a final item, then one surrounding fuel-driver step harvests
that item's `(atom, bindings)` readout.

This is the accumulator/bookkeeping part of the interpreter-correctness lift.  It is intentionally
generic and uses LeaTTa's proven `interpretFuel_done` accumulator theorem instead of unfolding a
concrete execution trace. -/
theorem mem_interpretFuel_single_of_mem_interpretStack1_final
    (env : MinEnv) (fuel : Nat) (st : St) (it out : Item)
    (hmem : out ∈ (interpretStack1 env fuel st it).1)
    (hfinal : isFinal out = true) :
    finalPair out ∈ (interpretFuel env (fuel + 1) st [it] []).1 := by
  cases hstep : interpretStack1 env fuel st it with
  | mk results st' =>
      simp only [interpretFuel, hstep, List.append_nil]
      rw [interpretFuel_done]
      have houtFiltered : out ∈ results.filter isFinal := by
        rw [List.mem_filter]
        exact ⟨by simpa [hstep] using hmem, hfinal⟩
      have houtFinals : finalPair out ∈ (results.filter isFinal).map finalPair := by
        exact List.mem_map.mpr ⟨out, houtFiltered, rfl⟩
      simp [houtFinals]

/-- Fuel-driver harvest of `interpretStack1_eval_notReducible_of_no_candidates`.

This is the generic executable side of constructor inertness: if the root evaluator frame reaches
the no-candidate branch, one surrounding fuel step harvests `NotReducible`. The outer `mettaEval`
loop then treats that marker as "keep the original atom"; this lemma supplies the reusable
fuel-driver half without unfolding concrete Peano traces. -/
theorem interpretFuel_eval_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hnone : candidatesW env st.world (Atom.expr (Atom.sym op :: args)) = []) :
    (notReducibleA, b) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] []).1 := by
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }
  let out : Item := finItem [] notReducibleA b
  have hmem : out ∈ (interpretStack1 env fuel st it).1 := by
    simpa [it, out] using
      interpretStack1_eval_notReducible_of_no_candidates env st fuel [] x b op args
        hinst hcall hembed hNotVarHead hnone
  have hfinal : isFinal out = true := by
    simp [out, finItem, isFinal]
  have hharvest :=
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal
  simpa [it, out, finItem, finalPair, instantiate_notReducibleA] using hharvest

/-- Exact fuel-driver form of `interpretFuel_eval_notReducible_of_no_candidates`: the structural
no-candidate branch harvests precisely `NotReducible` and preserves the state. -/
theorem interpretFuel_eval_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings)
    (op : String) (args : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hNotVarHead : isVariableHeaded (Atom.expr (Atom.sym op :: args)) = false)
    (hnone : candidatesW env st.world (Atom.expr (Atom.sym op :: args)) = []) :
    interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] [] =
      ([(notReducibleA, b)], st) := by
  have hstep := interpretStack1_eval_notReducible_of_no_candidates_eq
    env st fuel [] x b op args hinst hcall hembed hNotVarHead hnone
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA]

/-- Fuel-driver harvest of
`interpretStack1_eval_symbol_notReducible_of_no_candidates`. This is the executable root-evaluator
bridge for bare-symbol normal forms such as Peano `Z`. -/
theorem interpretFuel_eval_symbol_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (op : String)
    (hinst : instantiate b x = Atom.sym op)
    (hembed : isEmbeddedOp (Atom.sym op) = false)
    (hnone : candidatesW env st.world (Atom.sym op) = []) :
    (notReducibleA, b) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] []).1 := by
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }
  let out : Item := finItem [] notReducibleA b
  have hmem : out ∈ (interpretStack1 env fuel st it).1 := by
    simpa [it, out] using
      interpretStack1_eval_symbol_notReducible_of_no_candidates env st fuel [] x b op
        hinst hembed hnone
  have hfinal : isFinal out = true := by
    simp [out, finItem, isFinal]
  have hharvest :=
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal
  simpa [it, out, finItem, finalPair, instantiate_notReducibleA] using hharvest

/-- Exact fuel-driver form for bare-symbol no-candidate evaluation. -/
theorem interpretFuel_eval_symbol_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (op : String)
    (hinst : instantiate b x = Atom.sym op)
    (hembed : isEmbeddedOp (Atom.sym op) = false)
    (hnone : candidatesW env st.world (Atom.sym op) = []) :
    interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] [] =
      ([(notReducibleA, b)], st) := by
  have hstep := interpretStack1_eval_symbol_notReducible_of_no_candidates_eq
    env st fuel [] x b op hinst hembed hnone
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA]

/-! ## Full `mettaEval` consumption of `NotReducible` root readouts -/

private def mettaEvalBareFoldStep (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings) :
    List (Atom × Bindings) × St → Atom × Bindings → List (Atom × Bindings) × St :=
  fun a2 p =>
    if (p.1 == notReducibleA) = true ∨ (p.1 == w) = true then
      (a2.1 ++ [(w, bnd)], a2.2)
    else if returnsAtom env w = true ∧ isEmbeddedOp p.1 = false then
      (a2.1 ++ [p], a2.2)
    else
      (a2.1 ++ (mettaEval env fuel a2.2 p.2 p.1).1,
        (mettaEval env fuel a2.2 p.2 p.1).2)

private theorem mettaEvalBareFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (p : Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (hmem : (w, bnd) ∈ acc.1) :
    (w, bnd) ∈ (mettaEvalBareFoldStep env fuel w bnd acc p).1 := by
  unfold mettaEvalBareFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · split
    · exact List.mem_append.mpr (Or.inl hmem)
    · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalBareFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (acc : List (Atom × Bindings) × St) :
    (w, bnd) ∈ (mettaEvalBareFoldStep env fuel w bnd acc (notReducibleA, bnd)).1 := by
  have hbeq : (notReducibleA == notReducibleA) = true := rfl
  unfold mettaEvalBareFoldStep
  simp [hbeq]

private theorem mettaEvalBareFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hmem : (w, bnd) ∈ acc.1) :
    (w, bnd) ∈ (pairs.foldl (mettaEvalBareFoldStep env fuel w bnd) acc).1 := by
  induction pairs generalizing acc with
  | nil => simpa using hmem
  | cons p ps ih =>
      exact ih _ (mettaEvalBareFoldStep_preserves_mem env fuel w bnd p acc hmem)

private theorem mettaEvalBareFold_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (pairs : List (Atom × Bindings)) (st : St)
    (hmem : (notReducibleA, bnd) ∈ pairs) :
    (w, bnd) ∈ (pairs.foldl (mettaEvalBareFoldStep env fuel w bnd) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  exact mettaEvalBareFold_preserves_mem env fuel w bnd post _
    (mettaEvalBareFoldStep_hits_notReducible env fuel w bnd _)

/-- Full `mettaEval` keeps a bare symbol when the root minimal interpreter reports
`NotReducible`. This is the first outer-loop bridge above `interpretFuel`: the executable
`NotReducible` marker is consumed exactly as the interpreter specifies, without proving a
fuel-exact evaluator equality. -/
theorem mettaEval_symbol_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (op : String)
    (hreadout : (notReducibleA, bnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.sym op]) [], bnd := bnd }] []).1) :
    (Atom.sym op, bnd) ∈ (mettaEval env (fuel + 1) st bnd (Atom.sym op)).1 := by
  unfold mettaEval
  simp [Metta.instantiate, Metta.Subst.apply]
  cases hpairs : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.sym op]) [], bnd := bnd }] [] with
  | mk pairs st' =>
      simp only [hpairs] at hreadout ⊢
      exact mettaEvalBareFold_keeps_of_notReducible_readout env fuel (Atom.sym op) bnd pairs st'
        hreadout

/-- Exact version of `mettaEval_symbol_keeps_of_notReducible_readout` for the common structural
case where the root fuel driver returns exactly the singleton `NotReducible` readout and preserves
state. -/
theorem mettaEval_symbol_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (op : String)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.sym op]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.sym op) = ([(Atom.sym op, bnd)], st) := by
  unfold mettaEval
  simp [Metta.instantiate, Metta.Subst.apply]
  rw [hreadout]
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-- The inner fold used by `mettaEval` after evaluating a symbol-headed expression's arguments and
running the root `(eval w)` step.

Factoring it out lets corpus entries reason about the `NotReducible` case without re-expanding the
whole evaluator loop. -/
def mettaEvalExprRootFoldStep
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) :
    List (Atom × Bindings) × St → Atom × Bindings → List (Atom × Bindings) × St :=
  fun a2 p =>
    let pb := restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)
    if (p.1 == notReducibleA) = true ∨ (p.1 == w) = true then
      (a2.1 ++ [(w, partBnd)], a2.2)
    else if returnsAtom env w = true ∧ isEmbeddedOp p.1 = false then
      (a2.1 ++ [(p.1, pb)], a2.2)
    else
      let (more, st3) := mettaEval env fuel a2.2 pb p.1
      (a2.1 ++ more.map (fun m =>
        (m.1, restrictBnd queryVars ((Bindings.merge pb m.2).head?.getD m.2))), st3)

private theorem mettaEvalExprRootFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (p : Atom × Bindings)
    (acc : List (Atom × Bindings) × St)
    (hmem : (w, partBnd) ∈ acc.1) :
    (w, partBnd) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd acc p).1 := by
  unfold mettaEvalExprRootFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · split
    · exact List.mem_append.mpr (Or.inl hmem)
    · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalExprRootFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (acc : List (Atom × Bindings) × St)
    (rootBnd : Bindings) :
    (w, partBnd) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd acc
        (notReducibleA, rootBnd)).1 := by
  unfold mettaEvalExprRootFoldStep
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

private theorem mettaEvalExprRootFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hmem : (w, partBnd) ∈ acc.1) :
    (w, partBnd) ∈
      (pairs.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd) acc).1 := by
  induction pairs generalizing acc with
  | nil => simpa using hmem
  | cons p ps ih =>
      exact ih _ (mettaEvalExprRootFoldStep_preserves_mem env fuel queryVars w partBnd p acc hmem)

private theorem mettaEvalExprRootFoldStep_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (P : St → Prop)
    (hrec :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (p : Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (mettaEvalExprRootFoldStep env fuel queryVars w partBnd acc p).2 := by
  unfold mettaEvalExprRootFoldStep
  split
  · exact hacc
  · split
    · exact hacc
    · exact hrec acc p hacc

private theorem mettaEvalExprRootFold_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (P : St → Prop)
    (hrec :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (pairs.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd) acc).2 := by
  induction pairs generalizing acc with
  | nil => simpa using hacc
  | cons p ps ih =>
      exact ih _ (mettaEvalExprRootFoldStep_preserves_state_pred
        env fuel queryVars w partBnd P hrec p acc hacc)

theorem mettaEval_expr_root_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (rootBnd : Bindings)
    (pairs : List (Atom × Bindings)) (st : St)
    (hmem : (notReducibleA, rootBnd) ∈ pairs) :
    (w, partBnd) ∈
      (pairs.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  exact mettaEvalExprRootFold_preserves_mem env fuel queryVars w partBnd post _
    (mettaEvalExprRootFoldStep_hits_notReducible env fuel queryVars w partBnd _ rootBnd)

/-- Exact singleton form of the expression-root fold's `NotReducible` case. -/
theorem mettaEvalExprRootFold_eq_of_notReducible_singleton
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd rootBnd : Bindings) (st : St) :
    List.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd) ([], st)
        [(notReducibleA, rootBnd)] =
      ([(w, partBnd)], st) := by
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [mettaEvalExprRootFoldStep, hnr]

/-- The outer fold used by `mettaEval` after the argument-evaluation phase of a symbol-headed
expression.

The fold receives one binding-threaded partial application at a time, runs the root `(eval w)`
minimal-interpreter step, and either keeps `w`, returns an Atom-valued result, or recursively
evaluates the root readout. Naming the fold gives later soundness lemmas a stable abstraction
instead of re-expanding the whole evaluator. -/
def mettaEvalExprPartFoldStep
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) :
    List (Atom × Bindings) × St → List Atom × Bindings → List (Atom × Bindings) × St :=
  fun acc part =>
    match (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) with
    | some (err, _) => (acc.1 ++ [(err, part.2)], acc.2)
    | none =>
        let w := Atom.expr (Atom.sym op :: part.1)
        let (pairs, st') := interpretFuel env (fuel + 1) acc.2
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", w]) [], bnd := bnd }] []
        let (out, st'') := pairs.foldl
          (mettaEvalExprRootFoldStep env fuel queryVars w part.2) ([], st')
        (acc.1 ++ out, st'')

private theorem mettaEvalExprPartFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (part : List Atom × Bindings) (acc : List (Atom × Bindings) × St)
    {target : Atom × Bindings}
    (hmem : target ∈ acc.1) :
    target ∈
      (mettaEvalExprPartFoldStep env fuel queryVars op args bnd acc part).1 := by
  unfold mettaEvalExprPartFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalExprPartFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (parts : List (List Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    {target : Atom × Bindings}
    (hmem : target ∈ acc.1) :
    target ∈
      (parts.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) acc).1 := by
  induction parts generalizing acc with
  | nil => simpa using hmem
  | cons part parts ih =>
      exact ih _ (mettaEvalExprPartFoldStep_preserves_mem env fuel queryVars op args bnd part acc hmem)

private theorem mettaEvalExprPartFold_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (P : St → Prop)
    (hstep :
      ∀ (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings),
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd acc part).2)
    (parts : List (List Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (parts.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) acc).2 := by
  induction parts generalizing acc with
  | nil => simpa using hacc
  | cons part parts ih =>
      exact ih _ (hstep acc part hacc)

private theorem mettaEvalExprPartFoldStep_preserves_state_pred_of_root
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (P : St → Prop)
    (hroot :
      ∀ (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings),
        P acc.2 →
          P (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).2)
    (hrec :
      ∀ (partBnd : Bindings)
        (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings)
    (hacc : P acc.2) :
    P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd acc part).2 := by
  unfold mettaEvalExprPartFoldStep
  split
  · exact hacc
  · cases hpairs : interpretFuel env (fuel + 1) acc.2
      [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
          Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] [] with
    | mk pairs st' =>
        have hrootState : P st' := by
          have h := hroot acc part hacc
          rw [hpairs] at h
          simpa using h
        have hfold :
            P
              (List.foldl
                (mettaEvalExprRootFoldStep env fuel queryVars
                  (Atom.expr (Atom.sym op :: part.1)) part.2)
                ([], st') pairs).2 :=
          mettaEvalExprRootFold_preserves_state_pred env fuel queryVars
            (Atom.expr (Atom.sym op :: part.1)) part.2 P
            (fun acc p hP => hrec part.2 acc p hP)
            pairs ([], st') hrootState
        simpa [hpairs] using hfold

private theorem mettaEvalExprPartFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (part : List Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (rootBnd : Bindings)
    (hnoerr : (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none)
    (hroot : (notReducibleA, rootBnd) ∈
      (interpretFuel env (fuel + 1) acc.2
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
            Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).1) :
    (Atom.expr (Atom.sym op :: part.1), part.2) ∈
      (mettaEvalExprPartFoldStep env fuel queryVars op args bnd acc part).1 := by
  unfold mettaEvalExprPartFoldStep
  rw [hnoerr]
  simp only
  cases hpairs : interpretFuel env (fuel + 1) acc.2
      [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
          Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] [] with
  | mk pairs st' =>
      have hrootPairs : (notReducibleA, rootBnd) ∈ pairs := by
        rw [hpairs] at hroot
        simpa using hroot
      exact List.mem_append.mpr (Or.inr
        (by
          simpa using
            (mettaEval_expr_root_keeps_of_notReducible_readout
              env fuel queryVars (Atom.expr (Atom.sym op :: part.1)) part.2 rootBnd
              pairs st' hrootPairs)))

theorem mettaEvalExprPartFold_keeps_of_part_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (parts : List (List Atom × Bindings)) (init : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) (rootBnd : Bindings)
    (hpart : part ∈ parts)
    (hnoerr : (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none)
    (hroot :
      ∀ acc : List (Atom × Bindings) × St,
        (notReducibleA, rootBnd) ∈
          (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).1) :
    (Atom.expr (Atom.sym op :: part.1), part.2) ∈
      (parts.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) init).1 := by
  rcases List.mem_iff_append.mp hpart with ⟨pre, post, hparts⟩
  rw [hparts, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) init
  have hhit :=
    mettaEvalExprPartFoldStep_hits_notReducible
      env fuel queryVars op args bnd part accPre rootBnd hnoerr (hroot accPre)
  exact mettaEvalExprPartFold_preserves_mem env fuel queryVars op args bnd post _ hhit

/-- Invariant-aware form of `mettaEvalExprPartFold_keeps_of_part_notReducible`.

The selected partial may be processed after earlier partials have threaded the evaluator state.
Callers provide a state predicate `P`, a proof that the part fold preserves it, and a root readout
premise under `P`. This is the shape needed by the static-fragment runtime-correctness bridge:
the selected root step does not need to work for arbitrary states, only for states satisfying the
fragment invariant. -/
theorem mettaEvalExprPartFold_keeps_of_part_notReducible_of_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings)
    (P : St → Prop)
    (parts : List (List Atom × Bindings)) (init : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) (rootBnd : Bindings)
    (hinit : P init.2)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd acc part).2)
    (hpart : part ∈ parts)
    (hnoerr : (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none)
    (hroot :
      ∀ acc : List (Atom × Bindings) × St,
        P acc.2 →
          (notReducibleA, rootBnd) ∈
            (interpretFuel env (fuel + 1) acc.2
              [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                  Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).1) :
    (Atom.expr (Atom.sym op :: part.1), part.2) ∈
      (parts.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) init).1 := by
  rcases List.mem_iff_append.mp hpart with ⟨pre, post, hparts⟩
  rw [hparts, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd) init
  have haccPre : P accPre.2 :=
    mettaEvalExprPartFold_preserves_state_pred env fuel queryVars op args bnd P
      hstep pre init hinit
  have hhit :=
    mettaEvalExprPartFoldStep_hits_notReducible
      env fuel queryVars op args bnd part accPre rootBnd hnoerr (hroot accPre haccPre)
  exact mettaEvalExprPartFold_preserves_mem env fuel queryVars op args bnd post _ hhit

/-- The singleton work item used by the minimal interpreter to evaluate `a` with empty bindings. -/
def evalItemNil (a : Atom) : Item :=
  { stack := atomToStack (Atom.expr [Atom.sym "eval", a]) [] }

/-- One-argument constructor congruence for the executable `mettaEval` loop.

If the single argument of `(op arg)` evaluates to one readout `out`, and the rebuilt root
`(op out)` reports `NotReducible`, then the full evaluator keeps `(op out)`. This is the generic
outer-loop lemma needed by Peano-style constructors before proving a full evaluator computation
theorem; it avoids tracing one constructor layer at a time. -/
theorem mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp [hType, hMask, hArg, hNotError]
  have hrootDirect : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [({ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [] } :
          Item)] []).1 := by
    simpa [evalItemNil] using hroot
  cases hpairs : interpretFuel env (fuel + 1) stArg
      [({ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [] } :
        Item)] [] with
  | mk pairs stRoot =>
      have hrootPairs : (notReducibleA, []) ∈ pairs := by
        rw [hpairs] at hrootDirect
        simpa using hrootDirect
      change (Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
        (List.foldl
          (mettaEvalExprRootFoldStep env fuel arg.vars (Atom.expr [Atom.sym op, out])
            (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])))
          ([], stRoot) pairs).1
      exact
        mettaEval_expr_root_keeps_of_notReducible_readout
          env fuel (arg.vars) (Atom.expr [Atom.sym op, out])
          (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) [] pairs stRoot
          hrootPairs

/-- Membership-side soundness package for the unary constructor fold.

This is the non-exact counterpart of
`mettaEval_unary_expr_singleton_sound_of_arg_singleton_and_notReducible_eq`: it keeps the root
minimal-interpreter result as a membership premise and returns the actual outer readout together
with the caller-supplied certified relation chain under the constructor. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1)
    (hReach : Relation.ReflTransGen R
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
        (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out]) := by
  constructor
  · exact
      mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout
        env fuel st stArg op arg out hArg hType hMask hNotError hroot
  · exact hReach

/-- Unary constructor readout from a selected argument readout.

Unlike the singleton package above, this theorem allows the argument evaluator to return many
readouts.  The selected readout is followed through the argument-fold into the root-fold.  The root
`NotReducible` premise is quantified over every threaded state because earlier partials in the same
fold may have advanced the evaluator state before the selected partial is processed. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot :
      ∀ st0 : St,
        (notReducibleA, []) ∈
          (interpretFuel env (fuel + 1) st0
            [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  let parts : List (List Atom × Bindings) :=
    argPairs.map (fun p : Atom × Bindings =>
      ([p.1], restrictBnd arg.vars ((Bindings.merge [] p.2).head?.getD p.2)))
  let part : List Atom × Bindings :=
    ([out], restrictBnd arg.vars ((Bindings.merge [] ([] : Bindings)).head?.getD []))
  have hpart : part ∈ parts := by
    refine List.mem_map.mpr ⟨(out, []), hmemArg, ?_⟩
    simp [part]
  have hnoerr : (part.1.zip [arg]).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none := by
    simp [part, hNotError]
  have hrootPart :
      ∀ acc : List (Atom × Bindings) × St,
        (notReducibleA, []) ∈
          (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).1 := by
    intro acc
    simpa [part, evalItemNil] using hroot acc.2
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp only [hType, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hArg]
  simp
  change (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
    (parts.foldl (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [])
      ([], stArg)).1
  have hkeep := mettaEvalExprPartFold_keeps_of_part_notReducible
    env fuel arg.vars op [arg] [] parts ([], stArg) part []
    hpart hnoerr hrootPart
  simpa [part] using hkeep

/-- Invariant-aware selected-readout unary constructor theorem.

This is the preferred version for the static symbol-headed fragment. Earlier partials in the
argument/result fold may thread the evaluator state before the selected partial is processed, so
the root readout premise is stated under a state predicate `P`, together with a proof that the part
fold preserves `P`. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [] acc part).2)
    (hroot :
      ∀ st0 : St,
        P st0 →
          (notReducibleA, []) ∈
            (interpretFuel env (fuel + 1) st0
              [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  let parts : List (List Atom × Bindings) :=
    argPairs.map (fun p : Atom × Bindings =>
      ([p.1], restrictBnd arg.vars ((Bindings.merge [] p.2).head?.getD p.2)))
  let part : List Atom × Bindings :=
    ([out], restrictBnd arg.vars ((Bindings.merge [] ([] : Bindings)).head?.getD []))
  have hpart : part ∈ parts := by
    refine List.mem_map.mpr ⟨(out, []), hmemArg, ?_⟩
    simp [part]
  have hnoerr : (part.1.zip [arg]).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none := by
    simp [part, hNotError]
  have hrootPart :
      ∀ acc : List (Atom × Bindings) × St,
        P acc.2 →
          (notReducibleA, []) ∈
            (interpretFuel env (fuel + 1) acc.2
              [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                  Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).1 := by
    intro acc hP
    simpa [part, evalItemNil] using hroot acc.2 hP
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp only [hType, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hArg]
  simp
  change (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
    (parts.foldl (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [])
      ([], stArg)).1
  have hkeep := mettaEvalExprPartFold_keeps_of_part_notReducible_of_state_pred
    env fuel arg.vars op [arg] [] P parts ([], stArg) part []
    hinit hstep hpart hnoerr hrootPart
  simpa [part] using hkeep

/-- Relation-sound package for the selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot :
      ∀ st0 : St,
        (notReducibleA, []) ∈
          (interpretFuel env (fuel + 1) st0
            [evalItemNil (Atom.expr [Atom.sym op, out])] []).1)
    (hReach : Relation.ReflTransGen R
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
        (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out]) := by
  constructor
  · exact
      mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_all_states
        env fuel st stArg op arg out argPairs hArg hmemArg hType hMask hNotError hroot
  · exact hReach

/-- Relation-sound package for the invariant-aware selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (P : St → Prop) (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [] acc part).2)
    (hroot :
      ∀ st0 : St,
        P st0 →
          (notReducibleA, []) ∈
            (interpretFuel env (fuel + 1) st0
              [evalItemNil (Atom.expr [Atom.sym op, out])] []).1)
    (hReach : Relation.ReflTransGen R
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
        (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out]) := by
  constructor
  · exact
      mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred
        env fuel st stArg op arg out argPairs P hArg hmemArg hType hMask hNotError
        hinit hstep hroot
  · exact hReach

/-- Exact one-argument constructor congruence for the executable `mettaEval` loop.

This is still a one-layer theorem: callers provide the argument evaluator result and the rebuilt
root evaluator result. It is useful for inductive proofs, but it does not encode any concrete Peano
fuel arithmetic. -/
theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (arg out : Atom)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp [hType, hMask, hArg, hNotError]
  have hrootDirect :
      interpretFuel env (fuel + 1) stArg
        [({ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [] } :
          Item)] [] = ([(notReducibleA, [])], stRoot) := by
    simpa [evalItemNil] using hroot
  rw [hrootDirect]
  change
    List.foldl
        (mettaEvalExprRootFoldStep env fuel arg.vars (Atom.expr [Atom.sym op, out])
          (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])))
        ([], stRoot) [(notReducibleA, [])] =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot)
  exact mettaEvalExprRootFold_eq_of_notReducible_singleton
    env fuel arg.vars (Atom.expr [Atom.sym op, out])
    (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) [] stRoot

/-! ## Closed binary expression fold -/

/-- Closed two-argument outer-loop fold for the executable `mettaEval` evaluator.

This is the generic evaluator plumbing behind closed binary applications in the static fragment.
Callers provide:
* the actual evaluator results for both arguments;
* the root minimal-interpreter readout for the rebuilt application; and
* the recursive evaluation of that root readout.

The closed-argument hypotheses keep query-variable binding retention out of this theorem, which is
the first reusable binary fold needed by verified-MeTTa examples and SR-style kernel rules. -/
theorem mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hType : typeMismatch env st.world op [x, y] = none)
    (hMask : argMask env op 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom env (Atom.expr [Atom.sym op, x', y']) = false)
    (hFinal : mettaEval env fuel stRoot [] root = ([(final, [])], stOut)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(final, [])], stOut) := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x, y])]
  simp only [hType, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hx]
  simp [hxClosed, hyClosed, restrictBnd_nil_vars]
  rw [hy]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  have hRoot' :
      interpretFuel env (fuel + 1) st₂
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, x', y']]) [], bnd := [] }] [] =
      ([(root, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  simp [hRootNotNotReducible, hRootNotSelf, hReturns, hFinal]

/-- Membership-shaped closed binary expression fold for executable `mettaEval`.

This is the non-singleton companion to
`mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval`: callers still provide singleton
argument evaluator results and the root minimal-interpreter readout, but the recursive evaluation of
that root readout is consumed as a membership premise. This is the form needed when an induction
hypothesis gives an actual readout plus a certified relation chain, without requiring a singleton
equality for the recursive sub-run.

The closed-argument hypotheses force the retained output binding to `[]`; the theorem therefore
states the membership result at that binding rather than pretending arbitrary final bindings survive
the closed outer fold. -/
theorem mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hType : typeMismatch env st.world op [x, y] = none)
    (hMask : argMask env op 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom env (Atom.expr [Atom.sym op, x', y']) = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x, y])]
  simp only [hType, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hx]
  simp [hxClosed, hyClosed, restrictBnd_nil_vars]
  rw [hy]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  have hRoot' :
      interpretFuel env (fuel + 1) st₂
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, x', y']]) [], bnd := [] }] [] =
      ([(root, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  simp [hRootNotNotReducible, hRootNotSelf, hReturns]
  exact ⟨[], hFinal⟩

/-! ## Readout soundness packaging -/

/-- Package a singleton executable readout as a relation-sound readout theorem.

This small theorem is the reusable final step for examples and kernel rules: after a proof has
shown that the actual evaluator returns one readout, and a separate certified relation proof reaches
that readout, every actual output of that evaluator run is justified by the relation. -/
theorem mettaEval_singleton_readout_sound
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (atom out : Atom)
    (outBnd : Bindings) (stOut : St) (R : Atom → Atom → Prop)
    (hEval : mettaEval env fuel st bnd atom = ([(out, outBnd)], stOut))
    (hReach : Relation.ReflTransGen R atom out) :
    ∀ out' bnd',
      (out', bnd') ∈ (mettaEval env fuel st bnd atom).1 →
        bnd' = outBnd ∧ Relation.ReflTransGen R atom out' := by
  intro out' bnd' hout
  rw [hEval] at hout
  simp only [List.mem_singleton] at hout
  cases hout
  exact ⟨rfl, hReach⟩

/-- Soundness package for a unary expression whose evaluator result is obtained by the generic
constructor fold.

This is the reusable form of the "evaluate the subterm, rebuild the constructor, then show the
actual singleton readout is relation-sound" pattern.  Callers provide the relation chain under the
constructor; this theorem only connects that chain to the real `mettaEval` readout. -/
theorem mettaEval_unary_expr_singleton_sound_of_arg_singleton_and_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (arg out : Atom)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hType : typeMismatch env st.world op [arg] = none)
    (hMask : argMask env op 1 = [true])
    (hNotError : out.isError = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot))
    (hReach : Relation.ReflTransGen R
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])) :
    ∀ out' bnd',
      (out', bnd') ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 →
        bnd' = restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []) ∧
          Relation.ReflTransGen R (Atom.expr [Atom.sym op, arg]) out' := by
  have hEval :=
    mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq
      env fuel st stArg stRoot op arg out hArg hType hMask hNotError hroot
  exact
    mettaEval_singleton_readout_sound env (fuel + 1) st []
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])
      (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) stRoot R hEval hReach

/-- Soundness package for a closed binary expression whose evaluator result is obtained by the
generic binary fold.

The relation proof is split in the same way as the evaluator: a root relation chain from the
original application to the root readout, followed by a recursive relation chain from that root
readout to the final readout. -/
theorem mettaEval_binary_expr_singleton_sound_of_arg_singletons_and_root_eval
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hType : typeMismatch env st.world op [x, y] = none)
    (hMask : argMask env op 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom env (Atom.expr [Atom.sym op, x', y']) = false)
    (hFinal : mettaEval env fuel stRoot [] root = ([(final, [])], stOut))
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinalReach : Relation.ReflTransGen R root final) :
    ∀ out bnd,
      (out, bnd) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 →
        bnd = [] ∧ Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) out := by
  have hEval :=
    mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval
      env fuel st st₁ st₂ stRoot stOut op x y x' y' root final rootBnd
      hxClosed hyClosed hx hy hType hMask hNoErr hRoot hRootNotNotReducible
      hRootNotSelf hReturns hFinal
  exact
    mettaEval_singleton_readout_sound env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])
      final [] stOut R hEval (hRootReach.trans hFinalReach)

/-- Specific-member soundness package for a closed binary expression.

This is the induction-friendly counterpart of
`mettaEval_binary_expr_singleton_sound_of_arg_singletons_and_root_eval`.  The recursive evaluation of
the root readout is represented by one actual membership proof and the relation chain for that same
readout, not by singleton equality or Peano-specific fuel arithmetic. -/
theorem mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hType : typeMismatch env st.world op [x, y] = none)
    (hMask : argMask env op 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom env (Atom.expr [Atom.sym op, x', y']) = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalReach : Relation.ReflTransGen R root final) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final := by
  constructor
  · exact
      mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem
        env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
        hxClosed hyClosed hx hy hType hMask hNoErr hRoot hRootNotNotReducible hRootNotSelf
        hReturns hFinal
  · exact hRootReach.trans hFinalReach

/-- IH-shaped soundness package for a closed binary expression.

This version is convenient when an induction hypothesis provides soundness for every recursive
readout of the root result. It is a thin wrapper around the specific-member theorem above. -/
theorem mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hType : typeMismatch env st.world op [x, y] = none)
    (hMask : argMask env op 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom env (Atom.expr [Atom.sym op, x', y']) = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinalSound :
      ∀ final, (final, []) ∈ (mettaEval env fuel stRoot [] root).1 →
        Relation.ReflTransGen R root final)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final :=
  mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd R
    hxClosed hyClosed hx hy hType hMask hNoErr hRoot hRootNotNotReducible hRootNotSelf
    hReturns hRootReach hFinal (hFinalSound final hFinal)

/-- If one scheduler step returns exactly one non-final item, then one surrounding fuel-driver
step continues with that item.

This is the one-item recursive case of the work-list induction. -/
theorem interpretFuel_single_of_interpretStack1_single_nonfinal
    (env : MinEnv) (fuel : Nat) (st st' : St) (it out : Item)
    (hstep : interpretStack1 env fuel st it = ([out], st'))
    (hnonfinal : isFinal out = false) :
    interpretFuel env (fuel + 1) st [it] [] = interpretFuel env fuel st' [out] [] := by
  simp [interpretFuel, hstep, hnonfinal]

/-- Result-list form of `interpretFuel_single_of_interpretStack1_single_nonfinal`. It keeps the
threaded state abstract as the scheduler's second component, which is the right shape when a proof
tracks scheduler readouts before proving state-threading facts. -/
theorem interpretFuel_single_of_interpretStack1_results_single_nonfinal
    (env : MinEnv) (fuel : Nat) (st : St) (it out : Item)
    (hresults : (interpretStack1 env fuel st it).1 = [out])
    (hnonfinal : isFinal out = false) :
    interpretFuel env (fuel + 1) st [it] [] =
      interpretFuel env fuel (interpretStack1 env fuel st it).2 [out] [] := by
  cases hstep : interpretStack1 env fuel st it with
  | mk results st' =>
      simp only [hstep] at hresults ⊢
      subst hresults
      simp [interpretFuel, hstep, hnonfinal]

end Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
