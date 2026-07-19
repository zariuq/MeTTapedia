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

/-- A non-final top frame `(evalc x space)` delegates to `evalOp` in the environment selected by
the resolved space argument. -/
theorem interpretStack1_evalc_eq (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (x space : Atom) (b : Bindings) (evalEnv : MinEnv)
    (hspace : evalEnvForSpace env st.world (instantiate b space) = some evalEnv) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "evalc", x, space] } :: prev, bnd := b } =
      evalOp evalEnv st prev x b := by
  unfold interpretStack1
  simp [hspace]

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
    (prev : Stack) (x space : Atom) (b : Bindings) (evalEnv : MinEnv)
    (hspace : evalEnvForSpace env st.world (instantiate b space) = some evalEnv)
    (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "evalc", x, space] } :: prev, bnd := b }).1 ↔
      item ∈ (evalOp evalEnv st prev x b).1 := by
  rw [interpretStack1_evalc_eq env fuel st prev x space b evalEnv hspace]

/-! ## Scheduler control-flow boundary -/

/-- A non-final `(chain nested $v templ)` frame pushes the substituted continuation. -/
theorem interpretStack1_chain_eq (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (nested : Atom) (v : VarName) (templ : Atom) (b : Bindings) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] } :: prev,
          bnd := b } =
      ([{ stack := atomToStack (Metta.Subst.apply [(v, nested)] templ) prev, bnd := b }], st) := by
  unfold interpretStack1
  rfl

/-- Membership form of `interpretStack1_chain_eq`. -/
theorem mem_interpretStack1_chain_iff (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (nested : Atom) (v : VarName) (templ : Atom) (b : Bindings)
    (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] } :: prev,
          bnd := b }).1 ↔
      item = { stack := atomToStack (Metta.Subst.apply [(v, nested)] templ) prev, bnd := b } := by
  rw [interpretStack1_chain_eq]
  simp

/-- Returning from the nested child of a `chain` frame rewrites the parent to the resulting
continuation. -/
theorem interpretStack1_finished_chain_parent_eq (env : MinEnv) (fuel : Nat) (st : St)
    (pprev : Stack) (res nested : Atom) (v : VarName) (templ : Atom) (b : Bindings)
    (vars : List VarName) :
    interpretStack1 env fuel st
        { stack :=
            { atom := res, fin := true } ::
            { atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ],
              ret := Ret.chain, vars := vars } ::
            pprev,
          bnd := b } =
      ([{ stack :=
            { atom := Atom.expr [Atom.sym "chain", instantiate b res, Atom.var v, templ],
              ret := Ret.chain, vars := vars, fin := false } :: pprev,
          bnd := b }], st) := by
  unfold interpretStack1
  simp

/-- Membership form of `interpretStack1_finished_chain_parent_eq`. -/
theorem mem_interpretStack1_finished_chain_parent_iff
    (env : MinEnv) (fuel : Nat) (st : St)
    (pprev : Stack) (res nested : Atom) (v : VarName) (templ : Atom) (b : Bindings)
    (vars : List VarName) (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack :=
            { atom := res, fin := true } ::
            { atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ],
              ret := Ret.chain, vars := vars } ::
            pprev,
          bnd := b }).1 ↔
      item =
        { stack :=
            { atom := Atom.expr [Atom.sym "chain", instantiate b res, Atom.var v, templ],
              ret := Ret.chain, vars := vars, fin := false } :: pprev,
          bnd := b } := by
  rw [interpretStack1_finished_chain_parent_eq]
  simp

/-- A non-final `(unify a p t e)` frame delegates exactly to `unifyOp`. -/
theorem interpretStack1_unify_eq (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (a p t e : Atom) (b : Bindings) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "unify", a, p, t, e] } :: prev,
          bnd := b } =
      (unifyOp prev a p t e b, st) := by
  unfold interpretStack1
  rfl

/-- Membership form of `interpretStack1_unify_eq`. -/
theorem mem_interpretStack1_unify_iff (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (a p t e : Atom) (b : Bindings) (item : Item) :
    item ∈ (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "unify", a, p, t, e] } :: prev,
          bnd := b }).1 ↔
      item ∈ unifyOp prev a p t e b := by
  rw [interpretStack1_unify_eq]

/-- Successful matching and non-cyclic merge produce the instantiated `then` branch of `unifyOp`. -/
theorem mem_unifyOp_success_of_match_merge_noLoop
    (prev : Stack) (a p t e : Atom) (b mb m : Bindings)
    (hmatch : mb ∈ matchAtoms a p)
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false) :
    finItem prev (instantiate m t) m ∈ unifyOp prev a p t e b := by
  unfold unifyOp
  let ms := (matchAtoms a p).flatMap fun mb =>
    (Bindings.merge b mb).filterMap fun m =>
      if Bindings.hasLoop m then none else some (finItem prev (instantiate m t) m)
  have hmem_ms : finItem prev (instantiate m t) m ∈ ms := by
    dsimp [ms]
    apply List.mem_flatMap.mpr
    refine ⟨mb, hmatch, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨m, hmerge, ?_⟩
    simp [hloop]
  by_cases hempty : ms.isEmpty
  · have hnil : ms = [] := by
      simpa [List.isEmpty_iff] using hempty
    rw [hnil] at hmem_ms
    cases hmem_ms
  · simpa [ms, hempty] using hmem_ms

/-- If the local matcher has no results, `unifyOp` takes the explicit else branch. -/
theorem mem_unifyOp_fallback_of_matchAtoms_nil
    (prev : Stack) (a p t e : Atom) (b : Bindings)
    (hmatch : matchAtoms a p = []) :
    finItem prev e b ∈ unifyOp prev a p t e b := by
  unfold unifyOp
  simp [hmatch]

/-- Exact form of `mem_unifyOp_fallback_of_matchAtoms_nil`. -/
theorem unifyOp_fallback_eq_of_matchAtoms_nil
    (prev : Stack) (a p t e : Atom) (b : Bindings)
    (hmatch : matchAtoms a p = []) :
    unifyOp prev a p t e b = [finItem prev e b] := by
  unfold unifyOp
  simp [hmatch]

/-- Scheduler-level form of `mem_unifyOp_fallback_of_matchAtoms_nil`. -/
theorem interpretStack1_unify_fallback_of_matchAtoms_nil
    (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (a p t e : Atom) (b : Bindings)
    (hmatch : matchAtoms a p = []) :
    finItem prev e b ∈
      (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "unify", a, p, t, e] } :: prev,
          bnd := b }).1 := by
  exact
    (mem_interpretStack1_unify_iff env fuel st prev a p t e b (finItem prev e b)).2
      (mem_unifyOp_fallback_of_matchAtoms_nil prev a p t e b hmatch)

/-- Exact scheduler-level form of `unifyOp_fallback_eq_of_matchAtoms_nil`. -/
theorem interpretStack1_unify_fallback_eq_of_matchAtoms_nil
    (env : MinEnv) (fuel : Nat) (st : St)
    (prev : Stack) (a p t e : Atom) (b : Bindings)
    (hmatch : matchAtoms a p = []) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "unify", a, p, t, e] } :: prev,
          bnd := b } =
      ([finItem prev e b], st) := by
  rw [interpretStack1_unify_eq]
  simp [unifyOp_fallback_eq_of_matchAtoms_nil prev a p t e b hmatch]

/-! ## `evalOp` fall-through to equation lookup -/

/- The initial empty world has no token bindings, so token substitution is identity. -/
mutual
  theorem subTokens_init_world_eq_self : ∀ a : Atom, subTokens St.init.world a = a
    | Atom.sym s => by simp [subTokens, St.init, World.empty]
    | Atom.expr xs => by
        simp only [subTokens]
        rw [subTokens_init_world_list_eq_self xs]
    | Atom.var _ => by simp [subTokens]
    | Atom.gnd _ => by simp [subTokens]

  theorem subTokens_init_world_list_eq_self : ∀ xs : List Atom,
      xs.map (subTokens St.init.world) = xs
    | [] => by simp
    | x :: xs => by
        simp [subTokens_init_world_eq_self x, subTokens_init_world_list_eq_self xs]
end

/-- If grounded dispatch succeeds, `evalOp` emits exactly those grounded results as evaluated
items. -/
theorem evalOp_grounded_ok_eq
    (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args results : List Atom)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.ok results) :
    evalOp env st prev x b = (results.map (fun r => evalResult prev r b), st) := by
  unfold evalOp
  simp [hinst, hcall]

/-- Membership form of `evalOp_grounded_ok_eq`. -/
theorem mem_evalOp_grounded_ok_iff
    (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings)
    (op : String) (args results : List Atom) (item : Item)
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded env.gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.ok results) :
    item ∈ (evalOp env st prev x b).1 ↔
      item ∈ results.map (fun r => evalResult prev r b) := by
  rw [evalOp_grounded_ok_eq env st prev x b op args results hinst hcall]

private theorem extractRules_append
    (atoms extra : List Atom) :
    extractRules (atoms ++ extra) = extractRules atoms ++ extractRules extra := by
  simp [extractRules, List.filterMap_append]

/-- Candidate preservation for a statically indexed query when appended rules
cannot fire for that query's head.

This is the generic environment-monotonicity invariant used by the SR return path:
helper slices may append rules, but if those rules have neither the queried head key
nor a headless LHS, they do not change the executable candidate surface in the
initial static world. -/
theorem candidatesW_append_nonfiring_for_head
    {atoms extra : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String}
    (hhead : headKey toEval = some k)
    (hidx : (extractRules extra).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules extra).filter (fun r => (headKey r.1).isNone) = []) :
    candidatesW (MinEnv.ofAtomsGT (atoms ++ extra) gt) St.init.world toEval =
      candidatesW (MinEnv.ofAtomsGT atoms gt) St.init.world toEval := by
  have hrules := extractRules_append atoms extra
  simp [candidatesW, MinEnv.candidates, hhead, St.init, World.empty,
    Metta.ruleIndex_getD, Metta.ofAtomsGT_varRules, hrules, List.filter_append,
    hidx, hvar]

/-- Executable query monotonicity for helper slices that cannot fire on the queried head.

This lifts `candidatesW_append_nonfiring_for_head` to the real `queryOp` readout without
unfolding candidate folds or redoing matcher proofs. -/
theorem queryOp_append_nonfiring_for_head
    {atoms extra : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String} {prev : Stack} {b : Bindings}
    (hhead : headKey toEval = some k)
    (hidx : (extractRules extra).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules extra).filter (fun r => (headKey r.1).isNone) = []) :
    queryOp (MinEnv.ofAtomsGT (atoms ++ extra) gt) St.init prev toEval b =
      queryOp (MinEnv.ofAtomsGT atoms gt) St.init prev toEval b := by
  exact queryOp_eq_of_candidatesW_eq
    (candidatesW_append_nonfiring_for_head
      (atoms := atoms) (extra := extra) (gt := gt) (toEval := toEval) (k := k)
      hhead hidx hvar)

/-- Candidate preservation for a statically indexed query when prepended rules
cannot fire for that query's head.

This is the orientation used by environments of the form `prelude ++ core`: if the
prelude contributes neither rules for the queried head nor headless rules, loading
it before a core rule set leaves the core candidate surface unchanged. -/
theorem candidatesW_prepend_nonfiring_for_head
    {pre atoms : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String}
    (hhead : headKey toEval = some k)
    (hidx : (extractRules pre).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules pre).filter (fun r => (headKey r.1).isNone) = []) :
    candidatesW (MinEnv.ofAtomsGT (pre ++ atoms) gt) St.init.world toEval =
      candidatesW (MinEnv.ofAtomsGT atoms gt) St.init.world toEval := by
  have hrules := extractRules_append pre atoms
  simp [candidatesW, MinEnv.candidates, hhead, St.init, World.empty,
    Metta.ruleIndex_getD, Metta.ofAtomsGT_varRules, hrules, List.filter_append,
    hidx, hvar]

/-- Executable query monotonicity for prepended non-firing rule sets. -/
theorem queryOp_prepend_nonfiring_for_head
    {pre atoms : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String} {prev : Stack} {b : Bindings}
    (hhead : headKey toEval = some k)
    (hidx : (extractRules pre).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules pre).filter (fun r => (headKey r.1).isNone) = []) :
    queryOp (MinEnv.ofAtomsGT (pre ++ atoms) gt) St.init prev toEval b =
      queryOp (MinEnv.ofAtomsGT atoms gt) St.init prev toEval b := by
  exact queryOp_eq_of_candidatesW_eq
    (candidatesW_prepend_nonfiring_for_head
      (pre := pre) (atoms := atoms) (gt := gt) (toEval := toEval) (k := k)
      hhead hidx hvar)

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

/-- Immediate evaluator monotonicity for helper slices that cannot fire on the instantiated head.

This is the one-step runtime form of environment monotonicity: after grounded dispatch falls through
to the equality-rule query path on both environments, a non-firing append leaves the `evalOp` readout
unchanged. -/
theorem evalOp_append_nonfiring_for_head
    {atoms extra : List Atom} {gt : GroundingTable}
    {x : Atom} {k : String} {prev : Stack} {b : Bindings}
    {op : String} {args : List Atom}
    (hhead : headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hidx : (extractRules extra).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules extra).filter (fun r => (headKey r.1).isNone) = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcallApp : callGrounded (MinEnv.ofAtomsGT (atoms ++ extra) gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hcallCore : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    evalOp (MinEnv.ofAtomsGT (atoms ++ extra) gt) St.init prev x b =
      evalOp (MinEnv.ofAtomsGT atoms gt) St.init prev x b := by
  rw [evalOp_queryOp_of_instantiated_noReduce
      (env := MinEnv.ofAtomsGT (atoms ++ extra) gt) (st := St.init) (prev := prev)
      (x := x) (b := b) (op := op) (args := args) hinst hcallApp hembed,
    evalOp_queryOp_of_instantiated_noReduce
      (env := MinEnv.ofAtomsGT atoms gt) (st := St.init) (prev := prev)
      (x := x) (b := b) (op := op) (args := args) hinst hcallCore hembed]
  exact queryOp_append_nonfiring_for_head
    (atoms := atoms) (extra := extra) (gt := gt)
    (toEval := Atom.expr (Atom.sym op :: args)) (k := k) (prev := prev) (b := b)
    hhead hidx hvar

/-- Immediate evaluator monotonicity for prepended non-firing rule sets.

This is the `prelude ++ core` counterpart of `evalOp_append_nonfiring_for_head`: after grounded
dispatch falls through to the equality-rule query path on both environments, a non-firing pre
leaves the `evalOp` readout unchanged. -/
theorem evalOp_prepend_nonfiring_for_head
    {pre atoms : List Atom} {gt : GroundingTable}
    {x : Atom} {k : String} {prev : Stack} {b : Bindings}
    {op : String} {args : List Atom}
    (hhead : headKey (Atom.expr (Atom.sym op :: args)) = some k)
    (hidx : (extractRules pre).filter (fun r => headKey r.1 == some k) = [])
    (hvar : (extractRules pre).filter (fun r => (headKey r.1).isNone) = [])
    (hinst : instantiate b x = Atom.expr (Atom.sym op :: args))
    (hcallPrefix : callGrounded (MinEnv.ofAtomsGT (pre ++ atoms) gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hcallCore : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false) :
    evalOp (MinEnv.ofAtomsGT (pre ++ atoms) gt) St.init prev x b =
      evalOp (MinEnv.ofAtomsGT atoms gt) St.init prev x b := by
  rw [evalOp_queryOp_of_instantiated_noReduce
      (env := MinEnv.ofAtomsGT (pre ++ atoms) gt) (st := St.init) (prev := prev)
      (x := x) (b := b) (op := op) (args := args) hinst hcallPrefix hembed,
    evalOp_queryOp_of_instantiated_noReduce
      (env := MinEnv.ofAtomsGT atoms gt) (st := St.init) (prev := prev)
      (x := x) (b := b) (op := op) (args := args) hinst hcallCore hembed]
  exact queryOp_prepend_nonfiring_for_head
    (pre := pre) (atoms := atoms) (gt := gt)
    (toEval := Atom.expr (Atom.sym op :: args)) (k := k) (prev := prev) (b := b)
    hhead hidx hvar

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
    (hmatch : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) p.1 p.2).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false) :
    evalResult prev (instantiate m
        (freshenRuleAvoiding (st.counter + pre.length)
          (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) p.1 p.2).1.2) m ∈
      (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
    (MinEnv.ofAtomsGT atoms gt) fuel st prev x b op args
    (evalResult prev (instantiate m
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) p.1 p.2).1.2) m)
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
    (hmatchFresh : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev (instantiate m
        (freshenRuleAvoiding (st.counter + pre.length)
          (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.2) m ∈
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
    (hmatchFresh : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev (instantiate m
        (freshenRuleAvoiding (st.counter + pre.length)
          (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.2) m ∈
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
    (hmatchFresh : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge b mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hresult :
      instantiate m (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid prev (Atom.expr (Atom.sym op :: args)) b) lhs rhs).1.2 =
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
      pre ++ (Atom.var v, Atom.var v) :: post)
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) (.var v) (.var v)) :
    evalResult prev (Atom.expr (Atom.sym op :: args))
          [BindingRel.val (counterSuffix (st.counter + pre.length) v)
            (Atom.expr (Atom.sym op :: args))] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (Atom.expr (Atom.sym op :: args)) := by
  have hquery := queryOp_item_and_kernelStep_var_id_closed
    (st := st) (prev := prev) (toEval := Atom.expr (Atom.sym op :: args))
    (target := Atom.expr (Atom.sym op :: args)) (v := v) (pre := pre) (post := post)
    hclosed rfl hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit hcompat
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (Atom.expr (Atom.sym op :: args))
        [BindingRel.val (counterSuffix (st.counter + pre.length) v)
          (Atom.expr (Atom.sym op :: args))]) hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-- Scheduler-level variable-LHS crossing over a closed symbol-headed redex.

This is the one-variable RHS-general form of `interpretStack1_eval_var_id_closed`: the selected
static rule has LHS `$v`, the closed query supplies the singleton core binding `$v ↦ target`, and
all RHS variables are covered by that binding. The freshened executable item and the certified
`KernelStep` reduct therefore agree without an external result-equivalence premise. -/
theorem interpretStack1_eval_var_lhs_closed
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x rhs : Atom} {op v : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hclosed : (Atom.expr (Atom.sym op :: args)).vars = [])
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.var v, rhs) :: post)
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) (.var v) rhs)
    (hboundVars : ∀ w ∈ rhs.vars, w = v) :
    evalResult prev (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs)
          [BindingRel.val (counterSuffix (st.counter + pre.length) v)
            (Atom.expr (Atom.sym op :: args))] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args))
        (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) := by
  have hquery := queryOp_item_and_kernelStep_var_lhs_closed
    (st := st) (prev := prev) (target := Atom.expr (Atom.sym op :: args))
    (rhs := rhs) (v := v) (pre := pre) (post := post)
    hclosed hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit hcompat hboundVars
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs)
        [BindingRel.val (counterSuffix (st.counter + pre.length) v)
          (Atom.expr (Atom.sym op :: args))]) hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-- Scheduler-level open-target variable-LHS crossing.

This is the scheduler-facing counterpart of
`queryOp_item_and_kernelStep_var_lhs_open`: the selected rule has LHS `$v`, the queried target may
contain variables, and the two explicit freshness hypotheses exclude exactly the raw/fresh
same-variable cases where open-target matcher transport is false. -/
theorem interpretStack1_eval_var_lhs_open
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x rhs : Atom} {op v : String} {args : List Atom}
    {pre post : List (Atom × Atom)}
    (hraw : v ∉ (Atom.expr (Atom.sym op :: args)).vars)
    (hfresh : counterSuffix (st.counter + pre.length) v ∉
      (Atom.expr (Atom.sym op :: args)).vars)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.var v, rhs) :: post)
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) (.var v) rhs)
    (hboundVars : ∀ w ∈ rhs.vars, w = v) :
    evalResult prev (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs)
          [BindingRel.val (counterSuffix (st.counter + pre.length) v)
            (Atom.expr (Atom.sym op :: args))] ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args))
        (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) := by
  have hquery := queryOp_item_and_kernelStep_var_lhs_open
    (st := st) (prev := prev) (target := Atom.expr (Atom.sym op :: args))
    (rhs := rhs) (v := v) (pre := pre) (post := post)
    hraw hfresh hstatic (by simp [isVariableHeaded]) (by simp [headKey]) hsplit hcompat hboundVars
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs)
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
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
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
    hsplit hcompat (by rw [hcompat]; exact hmatchFresh) hmatchCore hbound
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (instantiate coreB rhs)
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse)
      hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-- Scheduler-level closed-target form of
`interpretStack1_eval_renamed_closed_coreBinding_reverse`: the runtime-freshened matcher witness is
derived from the core match instead of being supplied as a premise. -/
theorem interpretStack1_eval_renamed_closed_coreBinding_reverse_of_match
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
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
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t) :
    evalResult prev (instantiate coreB rhs)
          (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hquery := queryOp_item_and_kernelStep_of_renamed_closed_coreBinding_reverse_of_match
    (atoms := atoms) (gt := gt) (st := st) (prev := prev)
    (toEval := Atom.expr (Atom.sym op :: args)) (lhs := lhs) (rhs := rhs)
    (coreB := coreB) (pre := pre) (post := post)
    hclosedTarget hclosedB hnodup hstatic (by simp [isVariableHeaded]) (by simp [headKey])
    hsplit hcompat hmatchCore hbound
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev (instantiate coreB rhs)
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse)
      hinst hcall hembed]
    exact hquery.1
  · exact hquery.2

/-! ## Scheduler crossing for α-related runtime/certified results -/

/-- Scheduler-level α lift of
`queryOp_item_and_kernelStep_alpha_of_renamed_closed_coreBinding_reverse`.

This is the B1 crossing for rules whose RHS contains variables not bound by the matcher. The
runtime item carries the freshened executable RHS; the certified `KernelStep` carries the
unfreshened `firedReducts` RHS; `AlphaEq` records the canonical-core agreement. -/
theorem interpretStack1_eval_renamed_closed_coreBinding_reverse_alpha
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
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev
          (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
            (freshenRule (st.counter + pre.length) lhs rhs).2)
          (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  have hquery := queryOp_item_and_kernelStep_alpha_of_renamed_closed_coreBinding_reverse
    (atoms := atoms) (gt := gt) (st := st) (prev := prev)
    (toEval := Atom.expr (Atom.sym op :: args)) (lhs := lhs) (rhs := rhs)
    (coreB := coreB) (pre := pre) (post := post)
    hclosedB hnodup hstatic (by simp [isVariableHeaded]) (by simp [headKey])
    hsplit hcompat (by rw [hcompat]; exact hmatchFresh) hmatchCore
  rw [hcompat] at hquery
  constructor
  · rw [mem_interpretStack1_eval_queryOp_iff_of_instantiated_noReduce
      (MinEnv.ofAtomsGT atoms gt) fuel st prev x [] op args
      (evalResult prev
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse)
      hinst hcall hembed]
    exact hquery.1
  · exact ⟨hquery.2.1, hquery.2.2⟩

/-- Closed-target scheduler α form: matcher freshening is derived from the unfreshened core match,
leaving only the static split and closed binding shape as obligations. -/
theorem interpretStack1_eval_renamed_closed_coreBinding_reverse_alpha_of_match
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {prev : Stack} {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
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
    (hcompat : LegacyFresheningCompatible prev (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args))) :
    evalResult prev
          (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
            (freshenRule (st.counter + pre.length) lhs rhs).2)
          (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse ∈
        (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st
          { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := [] }).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  have hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)) :=
    matchAtoms_freshenRule_lhs_closed_target_mem
      (st.counter + pre.length) hclosedTarget hmatchCore
  exact interpretStack1_eval_renamed_closed_coreBinding_reverse_alpha
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := prev)
    (x := x) (lhs := lhs) (rhs := rhs) (coreB := coreB)
    (op := op) (args := args) (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore

/-! ## Scheduler crossing for the no-candidate `NotReducible` case -/

/-- Symbols are unaffected by instantiation under any binding set. -/
theorem instantiate_notReducibleA (b : Bindings) : instantiate b notReducibleA = notReducibleA := by
  simp [notReducibleA, instantiate, Bindings.resolveAtom]

/-- The scheduler's `NotReducible` marker survives v1.0.8's final `Empty` filtering. -/
theorem notReducibleA_ne_empty : (notReducibleA != emptyA) = true := by
  decide

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

/-- Grounded-atom version of `interpretStack1_eval_symbol_notReducible_of_no_candidates`.

Bare grounded atoms skip grounded function dispatch, enter `queryOp` directly, and reduce to
`NotReducible` when the current space has no matching candidate. This is the scheduler rung needed
for Boolean control-flow leaves such as `False` in embedded `unify` fallbacks. -/
theorem interpretStack1_eval_ground_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (g : Ground)
    (hinst : instantiate b x = Atom.gnd g)
    (hembed : isEmbeddedOp (Atom.gnd g) = false)
    (hnone : candidatesW env st.world (Atom.gnd g) = []) :
    finItem prev notReducibleA b ∈
      (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_iff]
  unfold evalOp
  simp [hinst, hembed]
  exact queryOp_contains_notReducible_of_no_candidates env st prev (Atom.gnd g) b
    (by simp [isVariableHeaded]) hnone

/-- Exact scheduler form for bare-grounded no-candidate evaluation. -/
theorem interpretStack1_eval_ground_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (g : Ground)
    (hinst : instantiate b x = Atom.gnd g)
    (hembed : isEmbeddedOp (Atom.gnd g) = false)
    (hnone : candidatesW env st.world (Atom.gnd g) = []) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      ([finItem prev notReducibleA b], st) := by
  rw [interpretStack1_eval_eq]
  unfold evalOp
  simp [hinst, hembed]
  exact queryOp_notReducible_of_no_candidates_eq env st prev (Atom.gnd g) b
    (by simp [isVariableHeaded]) hnone

/-- Bare-variable evaluation is guarded as variable-headed and emits `NotReducible`.

Unlike symbols and grounded atoms, this does not need a no-candidates premise: LeaTTa's `queryOp`
short-circuits variable-headed redexes before rule lookup so a bare query variable does not match
every equality rule. -/
theorem interpretStack1_eval_var_notReducible
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (v : VarName)
    (hinst : instantiate b x = Atom.var v)
    (hembed : isEmbeddedOp (Atom.var v) = false) :
    finItem prev notReducibleA b ∈
      (interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b }).1 := by
  rw [mem_interpretStack1_eval_iff]
  unfold evalOp
  simp [hinst, hembed, queryOp, isVariableHeaded]

/-- Exact scheduler form for bare-variable evaluation. -/
theorem interpretStack1_eval_var_notReducible_eq
    (env : MinEnv) (st : St) (fuel : Nat) (prev : Stack) (x : Atom) (b : Bindings)
    (v : VarName)
    (hinst : instantiate b x = Atom.var v)
    (hembed : isEmbeddedOp (Atom.var v) = false) :
    interpretStack1 env fuel st
        { stack := { atom := Atom.expr [Atom.sym "eval", x] } :: prev, bnd := b } =
      ([finItem prev notReducibleA b], st) := by
  rw [interpretStack1_eval_eq]
  unfold evalOp
  simp [hinst, hembed, queryOp, isVariableHeaded]

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
    (hfinal : isFinal out = true)
    (hnotEmpty : ((finalPair out).1 != emptyA) = true) :
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
      apply List.mem_append.mpr
      left
      apply List.mem_filter.mpr
      constructor
      ·
        rw [List.reverse_append, List.reverse_reverse]
        exact List.mem_append.mpr (Or.inr houtFinals)
      · exact hnotEmpty

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
  intro a hclosed
  exact instantiate_of_closed b a hclosed

/-- With no query variables to retain, LeaTTa's binding-retention pass drops every binding. This is
the argument-evaluation simplification used by closed programs such as Peano `add`: evaluated
closed arguments cannot leak internal fresh matcher bindings into the surrounding application. -/
theorem restrictBnd_nil_vars (b : Bindings) : restrictBnd [] b = [] := by
  unfold restrictBnd
  change b.filter (fun r => match r with | BindingRel.eq x y => false | _ => false) = []
  apply List.filter_eq_nil_iff.mpr
  intro r _hr
  cases r <;> simp

/-- Bare variables compare equal to themselves under LeaTTa's structural `BEq`.

This is intentionally only the variable fragment; `BEq Atom` is not globally lawful because
grounded floats inherit host IEEE equality. -/
theorem atom_var_beq_self_true (v : VarName) :
    (Atom.var v == Atom.var v) = true := by
  change Atom.beq (Atom.var v) (Atom.var v) = true
  simp [Atom.beq]

/-- Resolving a bare variable through the empty binding set is inert at any fuel depth. -/
theorem resolveAtom_nil_var (n : Nat) (v : VarName) :
    resolveAtom ([] : Bindings) n (Atom.var v) = Atom.var v := by
  induction n with
  | zero => rfl
  | succ _ _ =>
      simp [resolveAtom, Metta.instantiate_nil, atom_var_beq_self_true]

/-- Restricting the empty binding set to any query-variable list is empty. -/
theorem restrictBnd_nil_bindings (vars : List VarName) :
    restrictBnd vars ([] : Bindings) = [] := by
  simp [restrictBnd, resolveAtom_nil_var, atom_var_beq_self_true]

/-- Empty argument readouts remain empty after LeaTTa's merge-and-retain step, even when the
surrounding expression has query variables. -/
theorem restrictBnd_empty_merge_empty (vars : List VarName) :
    restrictBnd vars ((Bindings.merge [] ([] : Bindings)).head?.getD []) = [] := by
  simp [Bindings.merge, restrictBnd_nil_bindings]

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
    (hnotEmpty : (rhs != emptyA) = true)
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
        simpa [it, out] using hstep.1) hfinal (by
          simpa [out, heval, finItem, finalPair, Metta.instantiate_nil] using hnotEmpty)
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
    (hnotEmpty : (rhs != emptyA) = true)
    (hnotFunction : isFunctionResult rhs = false) :
    (rhs, []) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      KernelStep atoms gt (Atom.expr (Atom.sym op :: args)) rhs :=
  interpretFuel_eval_symbolic_rule_closed_contains_final
    hlhs hrhs hmatch hstatic hinst hcall hembed hsplit hnotEmpty
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
    (hnotEmpty : (rhs != emptyA) = true)
    (hnotFunction : isFunctionResult rhs = false) :
    (rhs, []) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) rhs := by
  rcases interpretFuel_eval_symbolic_rule_closed_contains_nonFunction
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (op := op) (args := args) (pre := pre) (post := post)
    hlhs hrhs hmatch hstatic hinst hcall hembed hsplit hnotEmpty hnotFunction with
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
    (hnotEmpty : (rhs != emptyA) = true)
    (hnotFunction : isFunctionResult rhs = false) :
    rhs ∈ evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) rhs := by
  rcases interpretFuel_eval_symbolic_rule_closed_contains_mops
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (op := op) (args := args) (pre := pre) (post := post)
    hlhs hrhs hmatch rfl hinst hcall hembed hsplit hnotEmpty hnotFunction with
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
    (hmatchFresh : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] (Atom.expr (Atom.sym op :: args)) []) lhs rhs).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge [] mb)
    (hloop : Bindings.hasLoop m = false)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hresult :
      instantiate m (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] (Atom.expr (Atom.sym op :: args)) []) lhs rhs).1.2 =
        instantiate coreB rhs)
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
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
        simpa [it, out] using hstep.1) hfinal (by
          simpa [out, heval, finItem, finalPair, hstable] using hnotEmpty)
  constructor
  · simpa [it, out, heval, finItem, finalPair, hstable] using hmemFuel
  · exact hstep.2

/-- Closed-binding convenience form of
`interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops`.

The exact-result theorem is intentionally general and therefore asks for the final-readout
stability premise explicitly.  In the runtime bridge's closed matcher fragment, that premise is
not extra data: it follows from closed-value substitution idempotence. -/
theorem interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops_of_closed_bindings
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
    (hmatchFresh : mb ∈ matchAtoms
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] (Atom.expr (Atom.sym op :: args)) []) lhs rhs).1.1
      (Atom.expr (Atom.sym op :: args)))
    (hmerge : m ∈ Bindings.merge [] mb)
    (hloop : Bindings.hasLoop m = false)
    (hclosedM : ClosedValueBindings m)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hresult :
      instantiate m (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] (Atom.expr (Atom.sym op :: args)) []) lhs rhs).1.2 =
        instantiate coreB rhs)
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs, m) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      ExprCtxMopsStep atoms (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hstable : instantiate m (instantiate coreB rhs) = instantiate coreB rhs := by
    rw [← hresult]
    exact instantiate_closed_value_bindings_idempotent hclosedM
      (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] (Atom.expr (Atom.sym op :: args)) []) lhs rhs).1.2
  exact interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (mb := mb) (m := m) (coreB := coreB)
    (op := op) (args := args) (pre := pre) (post := post)
    hstatic hinst hcall hembed hNotVarHead hhead hsplit hmatchFresh hmerge hloop
    hmatchCore hresult hnotEmpty hnotFunction hstable

/-
The legacy open exact-list runtime crossings are false after equality-class repair. Variable-valued
relations normalize to `eq` during merge, and origin-blind renaming does not transport those classes.
/-- Open-value version of the fuel-driver static-candidate crossing.

This is the reusable fuel-level surface for open matcher values: the binding set need not be closed,
but the runtime-renamed value keys must be fresh for all values they carry. Under that invariant,
empty-ambient merge, loop pruning, freshened-RHS equality, and final-readout stability are all
discharged once, rather than supplied as per-rule premises. Matcher equivariance (`hmatchFresh`) is
still explicit; callers that know a source-specific matcher theorem should discharge it separately. -/
theorem interpretFuel_eval_renamed_value_coreBinding_reverse_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hvalB : ValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hfreshValues :
      RenamedValueKeysFreshForValues (counterSuffix (st.counter + pre.length)) coreB)
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
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  let f := counterSuffix (st.counter + pre.length)
  have hf : Function.Injective f := by
    simpa [f] using counterSuffix_injective (st.counter + pre.length)
  have hvalRen : ValueBindings (renameBindings f coreB) := ValueBindings.rename hvalB
  have hnodupRen : (bindingValueKeys (renameBindings f coreB)).Nodup := by
    rw [bindingValueKeys_renameBindings]
    exact List.Nodup.map hf hnodup
  have hmerge : (renameBindings f coreB).reverse ∈ Bindings.merge [] (renameBindings f coreB) := by
    exact merge_empty_renamed_value_nodup_mem hf hvalB hnodup
  have hloop : Bindings.hasLoop (renameBindings f coreB).reverse = false := by
    exact ValueBindings.rename_reverse_hasLoop_false_of_not_mem_vars hvalB (by
      intro key value hmem
      simpa [f] using renamedValueKeysFreshForValues_self hfreshValues key value hmem)
  have hreverseInst :
      instantiate (renameBindings f coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2 =
        instantiate (renameBindings f coreB) (freshenRule (st.counter + pre.length) lhs rhs).2 :=
    instantiate_reverse_value_nodup hvalRen hnodupRen _
  have hfreshInst :
      instantiate (renameBindings f coreB) (freshenRule (st.counter + pre.length) lhs rhs).2 =
        instantiate coreB rhs := by
    simpa [f] using instantiate_freshenRule_rhs_of_renamed_bindings
      (st.counter + pre.length) lhs rhs coreB hbound
  have hresult :
      instantiate (renameBindings f coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2 =
        instantiate coreB rhs := by
    rw [hreverseInst, hfreshInst]
  have hstable :
      instantiate (renameBindings f coreB).reverse (instantiate coreB rhs) =
        instantiate coreB rhs := by
    simpa [f] using instantiate_renamed_reverse_stable_after_value_subst
      hf hvalB hnodup hfreshValues rhs hbound
  rcases interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops
      (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
      (lhs := lhs) (rhs := rhs) (mb := renameBindings f coreB)
      (m := (renameBindings f coreB).reverse) (coreB := coreB)
      (op := op) (args := args) (pre := pre) (post := post)
      hstatic hinst hcall hembed (by simp [isVariableHeaded]) (by simp [headKey])
      hsplit (by simpa [f] using hmatchFresh) (by simpa [f] using hmerge)
      (by simpa [f] using hloop) hmatchCore hresult hnotEmpty hnotFunction hstable with
    ⟨hmem, hstep⟩
  exact ⟨by simpa [f] using hmem, Relation.ReflTransGen.single hstep⟩

/-- Source-origin open-target form of
`interpretFuel_eval_renamed_value_coreBinding_reverse_contains_mops`.

This discharges the matcher-equivariance premise from `LeftPatternShape`, then reuses the existing
fuel-level open-value crossing. -/
theorem interpretFuel_eval_renamed_value_coreBinding_reverse_contains_mops_of_leftPattern
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hshape : LeftPatternShape (counterSuffix (st.counter + pre.length)) lhs
      (Atom.expr (Atom.sym op :: args)))
    (hvalB : ValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hfreshValues :
      RenamedValueKeysFreshForValues (counterSuffix (st.counter + pre.length)) coreB)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hmatchFresh :
      renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
        matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
          (Atom.expr (Atom.sym op :: args)) :=
    matchAtoms_freshenRule_lhs_leftPattern_mem
      (st.counter + pre.length) hshape hmatchCore
  exact interpretFuel_eval_renamed_value_coreBinding_reverse_contains_mops
    (hvalB := hvalB) (hnodup := hnodup) (hfreshValues := hfreshValues)
    (hstatic := hstatic) (hinst := hinst) (hcall := hcall) (hembed := hembed)
    (hsplit := hsplit) (hmatchFresh := hmatchFresh)
    (hmatchCore := hmatchCore) (hbound := hbound) (hnotEmpty := hnotEmpty)
    (hnotFunction := hnotFunction)

-/

/-- Fuel-driver harvest of the generic renamed-core binding crossing when the emitted RHS is
already final.

This is the first B2 theorem that composes the generic B1 crossing all the way through a real
`interpretFuel` readout: the scheduler emits a final item, the fuel driver harvests it, and the
certified root step is returned as a `ReflTransGen KernelStep` chain. The returned atom is the
actual `finalPair` projection, namely the certified reduct after the harvested bindings are applied
once more. Closed-result wrappers below collapse that projection back to the certified reduct. -/
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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (instantiate coreB rhs) != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (instantiate coreB rhs),
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
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
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
        simpa [it, out, m] using hstep.1) hfinal (by
          simpa [out, heval, finItem, finalPair, m] using hnotEmpty)
  constructor
  · simpa [it, out, heval, finItem, finalPair, m] using hmemFuel
  · exact Relation.ReflTransGen.single hstep.2

/-- Fuel-driver harvest of the α-shaped renamed-core crossing.

This is the `interpretFuel` counterpart of
`interpretStack1_eval_renamed_closed_coreBinding_reverse_alpha`: the actual executable readout is
the runtime-freshened RHS, while the certified `KernelStep` target is the unfreshened RHS. They are
kept separate and related by `AlphaEq`; no raw-name equality is forced. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final
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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2 != emptyA) = true)
    (hnotFunction :
      isFunctionResult
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2) = false) :
    (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2,
      (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep atoms gt)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  let m : Bindings := (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
  let actual : Atom := instantiate m (freshenRule (st.counter + pre.length) lhs rhs).2
  let certified : Atom := instantiate coreB rhs
  have hstep := interpretStack1_eval_renamed_closed_coreBinding_reverse_alpha
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (prev := [])
    (x := x) (lhs := lhs) (rhs := rhs) (coreB := coreB)
    (op := op) (args := args) (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }
  let out : Item := evalResult [] actual m
  have hmemStack : out ∈ (interpretStack1 (MinEnv.ofAtomsGT atoms gt) fuel st it).1 := by
    simpa [it, out, actual, m] using hstep.1
  have heval : out = finItem [] actual m := by
    simpa [out, actual, m] using
      (evalResult_nil_eq_finItem_of_not_function
        (a := actual) (b := m) (by simpa [actual, m] using hnotFunction))
  have hfinal : isFinal out = true := by
    simp [out, heval, finItem, isFinal]
  have hclosedRen :
      ClosedValueBindings (renameBindings (counterSuffix (st.counter + pre.length)) coreB) :=
    ClosedValueBindings.rename hclosedB
  have hclosedM : ClosedValueBindings m := by
    simpa [m] using ClosedValueBindings.reverse hclosedRen
  have hstable : instantiate m actual = actual := by
    simpa [actual] using
      instantiate_closed_value_bindings_idempotent hclosedM
        (freshenRule (st.counter + pre.length) lhs rhs).2
  have hmemFuel :
      finalPair out ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st [it] []).1 :=
    mem_interpretFuel_cons_final_of_mem_interpretStack1
      (MinEnv.ofAtomsGT atoms gt) fuel st it out [] [] hmemStack hfinal (by
        simpa [out, heval, finItem, finalPair, actual, m, hstable] using hnotEmpty)
  constructor
  · simpa [it, out, heval, finItem, finalPair, actual, m, hstable] using hmemFuel
  · exact ⟨Relation.ReflTransGen.single hstep.2.1,
      by simpa [actual, certified, m] using hstep.2.2⟩

/-- MOPS-facing form of
`interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final`.

This is the reusable Gate-2 bridge for static symbol-headed rules whose runtime
readout differs from the certified reduct only by rule-variable freshening:
`interpretFuel` returns the actual freshened atom, MOPS reaches the certified
unfreshened reduct, and the two are related by LeaTTa's canonical `AlphaEq`. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops
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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2 != emptyA) = true)
    (hnotFunction :
      isFunctionResult
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2) = false) :
    (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2,
      (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (MopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore
    hnotEmpty hnotFunction with
    ⟨hmem, hkernel, halpha⟩
  exact
    ⟨hmem,
      (reflTransGen_kernelStep_iff_mops atoms gt
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs)).1 hkernel,
      halpha⟩

/-- MOPS-facing alpha form with the matcher-freshening premise discharged by
the generic closed-target matcher-renaming theorem. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops_of_match
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
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
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2 != emptyA) = true)
    (hnotFunction :
      isFunctionResult
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2) = false) :
    (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
        (freshenRule (st.counter + pre.length) lhs rhs).2,
      (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (MopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse
          (freshenRule (st.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  have hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)) :=
    matchAtoms_freshenRule_lhs_closed_target_mem
      (st.counter + pre.length) hclosedTarget hmatchCore
  have hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs := by
    apply legacyFresheningCompatible_of_no_collision
    simp [QueryOpBridge.queryOpAvoid, Metta.Minimal.queryOpAvoid, Bindings.vars,
      liveStackVars, hclosedTarget]
  exact interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore
    hnotEmpty hnotFunction

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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep atoms gt)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hbase :=
    interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_final
      (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
      (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
      (pre := pre) (post := post)
      hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
      (by simpa [instantiate_eq_self_of_vars_nil _ hclosedResult] using hnotEmpty)
      hnotFunction
  simpa [instantiate_eq_self_of_vars_nil _ hclosedResult] using hbase

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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
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
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
    hclosedResult hnotEmpty hnotFunction with
    ⟨hmem, hreach⟩
  exact ⟨hmem,
    exprCtxKernelChain_to_mops (kernelChain_to_exprCtxKernelChain hreach)⟩

/-- MOPS-facing closed-result form with the matcher-freshening premise discharged by the generic
closed-target matcher-renaming theorem. -/
theorem interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops_of_match
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
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
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    (instantiate coreB rhs,
        (renameBindings (counterSuffix (st.counter + pre.length)) coreB).reverse) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  have hmatchFresh : renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (st.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)) :=
    matchAtoms_freshenRule_lhs_closed_target_mem
      (st.counter + pre.length) hclosedTarget hmatchCore
  have hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) lhs rhs := by
    apply legacyFresheningCompatible_of_no_collision
    simp [QueryOpBridge.queryOpAvoid, Metta.Minimal.queryOpAvoid, Bindings.vars,
      liveStackVars, hclosedTarget]
  exact interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
    hclosedResult hnotEmpty hnotFunction

/-- Fuel-driver harvest for a static variable-LHS rule over a closed symbol-headed redex.

This is a no-`hresult`/no-`hstable` specialization of the renamed-core bridge: the core binding is
the singleton `$v ↦ target`, runtime freshening only renames that binding key, and a closed final
reduct is stable under the harvested binding set. -/
theorem interpretFuel_eval_var_lhs_closed_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x rhs : Atom} {op v : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.var v, rhs) :: post)
    (hboundVars : ∀ w ∈ rhs.vars, w = v)
    (hclosedResult :
      (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs).vars = [])
    (hnotEmpty :
      (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs != emptyA) = true)
    (hnotFunction :
      isFunctionResult (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) =
        false) :
    (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs,
        [BindingRel.val (counterSuffix (st.counter + pre.length) v)
          (Atom.expr (Atom.sym op :: args))]) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args))
        (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) := by
  let target := Atom.expr (Atom.sym op :: args)
  let coreB : Bindings := [BindingRel.val v target]
  have hclosedB : ClosedValueBindings coreB := by
    exact ClosedValueBindings.val (by simpa [target] using hclosedTarget) ClosedValueBindings.nil
  have hnodup : (bindingValueKeys coreB).Nodup := by
    simp [coreB, bindingValueKeys]
  have hmatchFresh :
      renameBindings (counterSuffix (st.counter + pre.length)) coreB ∈
        matchAtoms (freshenRule (st.counter + pre.length) (Atom.var v) rhs).1 target := by
    have hfr := freshenRule_eq_renBy (st.counter + pre.length) (Atom.var v) rhs
    rw [hfr]
    simp [coreB, target, renameBindings]
    exact matchAtoms_var_closed_mem (counterSuffix (st.counter + pre.length) v)
      (Atom.expr (Atom.sym op :: args)) hclosedTarget
  have hmatchCore : coreB ∈ matchAtoms (Atom.var v) target := by
    simpa [coreB, target] using
      matchAtoms_var_closed_mem v (Atom.expr (Atom.sym op :: args)) hclosedTarget
  have hbound : ∀ w ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB w = some t := by
    intro w hw
    have hwv : w = v := hboundVars w hw
    subst hwv
    exact ⟨target, by simp [coreB, target, Bindings.lookupVal]⟩
  have hcompat : LegacyFresheningCompatible [] target []
      (st.counter + pre.length) (.var v) rhs := by
    apply legacyFresheningCompatible_of_no_collision
    simp [QueryOpBridge.queryOpAvoid, Metta.Minimal.queryOpAvoid, Bindings.vars,
      liveStackVars, target, hclosedTarget]
  simpa [coreB, target, renameBindings] using
    (interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops
      (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
      (lhs := Atom.var v) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
      (pre := pre) (post := post)
      hclosedB hnodup hstatic hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
      (by simpa [coreB, target] using hclosedResult)
      (by simpa [coreB, target] using hnotEmpty)
      (by simpa [coreB, target] using hnotFunction))

/-- Fuel-driver harvest for a static variable-LHS rule over an open symbol-headed redex.

This is the fuel-level counterpart of `interpretStack1_eval_var_lhs_open`. The two freshness
hypotheses exclude exactly the open-target matcher counterexamples: the queried redex is neither the
raw rule variable nor the runtime-freshened rule variable. The final-readout stability side condition
is discharged structurally from the RHS variable discipline instead of by exact fuel computation. -/
theorem interpretFuel_eval_var_lhs_open_contains_mops
    {atoms : List Atom} {gt : GroundingTable} {st : St} {fuel : Nat}
    {x rhs : Atom} {op v : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hraw : v ∉ (Atom.expr (Atom.sym op :: args)).vars)
    (hfresh : counterSuffix (st.counter + pre.length) v ∉
      (Atom.expr (Atom.sym op :: args)).vars)
    (hstatic : st.world.selfExtra = [])
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates st.world (subTokens st.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (Atom.var v, rhs) :: post)
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (st.counter + pre.length) (.var v) rhs)
    (hboundVars : ∀ w ∈ rhs.vars, w = v)
    (hnotEmpty :
      (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs != emptyA) = true)
    (hnotFunction :
      isFunctionResult (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) =
        false) :
    (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs,
        [BindingRel.val (counterSuffix (st.counter + pre.length) v)
          (Atom.expr (Atom.sym op :: args))]) ∈
        (interpretFuel (MinEnv.ofAtomsGT atoms gt) (fuel + 1) st
          [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := [] }] []).1 ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args))
        (instantiate [BindingRel.val v (Atom.expr (Atom.sym op :: args))] rhs) := by
  let target := Atom.expr (Atom.sym op :: args)
  let fresh := counterSuffix (st.counter + pre.length) v
  let coreB : Bindings := [BindingRel.val v target]
  have htargetNotVar : ∀ w, target ≠ Atom.var w := by
    intro w
    simp [target]
  have hmatchFresh : [BindingRel.val fresh target] ∈
      matchAtoms (freshenRule (st.counter + pre.length) (Atom.var v) rhs).1 target := by
    have hfr := freshenRule_eq_renBy (st.counter + pre.length) (Atom.var v) rhs
    rw [hfr]
    simp [fresh, target]
    exact matchAtoms_var_not_mem (counterSuffix (st.counter + pre.length) v)
      (Atom.expr (Atom.sym op :: args)) hfresh (by intro w; simp)
  have hmerge : [BindingRel.val fresh target] ∈
      Bindings.merge [] [BindingRel.val fresh target] := by
    exact singleton_val_mem_merge_empty_left fresh target htargetNotVar
  have hloop : Bindings.hasLoop [BindingRel.val fresh target] = false := by
    exact hasLoop_singleton_val_not_false fresh target (by simpa [fresh, target] using hfresh)
  have hmatchCore : coreB ∈ matchAtoms (Atom.var v) target := by
    simpa [coreB, target] using
      matchAtoms_var_not_mem v (Atom.expr (Atom.sym op :: args)) hraw
  have hbound : ∀ w ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB w = some t := by
    intro w hw
    have hwv : w = v := hboundVars w hw
    subst hwv
    exact ⟨target, by simp [coreB, target, Bindings.lookupVal]⟩
  have hresult :
      instantiate [BindingRel.val fresh target]
          (freshenRule (st.counter + pre.length) (Atom.var v) rhs).2 =
        instantiate coreB rhs := by
    simpa [coreB, fresh, target, renameBindings] using
      (instantiate_freshenRule_rhs_of_renamed_bindings
        (st.counter + pre.length) (Atom.var v) rhs coreB
        (by exact ValueBindings.val ValueBindings.nil)
        (by simpa [coreB, target] using singleton_valueKeysFreshForValues hraw)
        (by simpa [coreB, target, fresh] using
          singleton_renamedValueKeysFreshForValues (counterSuffix (st.counter + pre.length)) hfresh)
        hbound)
  have hstable :
      instantiate [BindingRel.val fresh target] (instantiate coreB rhs) = instantiate coreB rhs := by
    simpa [coreB, fresh, target] using
      (instantiate_singleton_val_stable_after_singleton_subst
        (counterSuffix (st.counter + pre.length) v) v (Atom.expr (Atom.sym op :: args))
        hfresh hraw (rhs := rhs) hboundVars)
  have hmatchFreshActual : [BindingRel.val fresh target] ∈
      matchAtoms (freshenRuleAvoiding (st.counter + pre.length)
        (QueryOpBridge.queryOpAvoid [] target []) (Atom.var v) rhs).1.1 target := by
    rw [hcompat]
    exact hmatchFresh
  have hresultActual :
      instantiate [BindingRel.val fresh target]
          (freshenRuleAvoiding (st.counter + pre.length)
            (QueryOpBridge.queryOpAvoid [] target []) (Atom.var v) rhs).1.2 =
        instantiate coreB rhs := by
    rw [hcompat]
    exact hresult
  have hbase := interpretFuel_eval_staticCandidateSplit_eqResult_contains_mops
    (atoms := atoms) (gt := gt) (st := st) (fuel := fuel) (x := x)
    (lhs := Atom.var v) (rhs := rhs)
    (mb := [BindingRel.val fresh target])
    (m := [BindingRel.val fresh target])
    (coreB := coreB) (op := op) (args := args) (pre := pre) (post := post)
    hstatic hinst hcall hembed (by simp [isVariableHeaded]) (by simp [headKey])
    hsplit hmatchFreshActual hmerge hloop hmatchCore hresultActual
    (by simpa [coreB, target] using hnotEmpty)
    (by simpa [coreB, target] using hnotFunction) hstable
  constructor
  · simpa [coreB, target, fresh] using hbase.1
  · exact Relation.ReflTransGen.single hbase.2

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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (St.init.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (St.init.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (St.init.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hbound : ∀ v ∈ rhs.vars, ∃ t, Bindings.lookupVal coreB v = some t)
    (hclosedResult : (instantiate coreB rhs).vars = [])
    (hnotEmpty : (instantiate coreB rhs != emptyA) = true)
    (hnotFunction : isFunctionResult (instantiate coreB rhs) = false) :
    instantiate coreB rhs ∈ evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (ExprCtxMopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed_mops
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup rfl hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore hbound
    hclosedResult hnotEmpty hnotFunction with
    ⟨hmem, hreach⟩
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr
      ⟨(instantiate coreB rhs,
          (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse),
        by simpa [atomToStack_eval] using hmem, rfl⟩
  · exact hreach

/-- Public minimal-evaluator α form of
`interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops`.

This is the compact Gate-2 surface for static symbol-headed rules with
freshened escaping RHS variables: the executable minimal evaluator emits the
runtime-freshened readout, the certified MOPS relation reaches the unfreshened
reduct, and the two atoms agree up to `AlphaEq`. -/
theorem evalAtomMin_renamed_closed_coreBinding_reverse_alpha_mops
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
    (hcompat : LegacyFresheningCompatible [] (Atom.expr (Atom.sym op :: args)) []
      (St.init.counter + pre.length) lhs rhs)
    (hmatchFresh : renameBindings (counterSuffix (St.init.counter + pre.length)) coreB ∈
      matchAtoms (freshenRule (St.init.counter + pre.length) lhs rhs).1
        (Atom.expr (Atom.sym op :: args)))
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
        (freshenRule (St.init.counter + pre.length) lhs rhs).2 != emptyA) = true)
    (hnotFunction :
      isFunctionResult
        (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2) = false) :
    instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
        (freshenRule (St.init.counter + pre.length) lhs rhs).2 ∈
        evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (MopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedB hnodup rfl hinst hcall hembed hsplit hcompat hmatchFresh hmatchCore
    hnotEmpty hnotFunction with
    ⟨hmem, hreach, halpha⟩
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr
      ⟨(instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2,
        (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse),
        by simpa [atomToStack_eval] using hmem, rfl⟩
  · exact ⟨hreach, halpha⟩

/-- Public minimal-evaluator alpha form with matcher freshening discharged for
closed static targets. -/
theorem evalAtomMin_renamed_closed_coreBinding_reverse_alpha_mops_of_match
    {atoms : List Atom} {gt : GroundingTable} {fuel : Nat}
    {x lhs rhs : Atom} {coreB : Bindings}
    {op : String} {args : List Atom} {pre post : List (Atom × Atom)}
    (hclosedTarget : (Atom.expr (Atom.sym op :: args)).vars = [])
    (hclosedB : ClosedValueBindings coreB)
    (hnodup : (bindingValueKeys coreB).Nodup)
    (hinst : instantiate [] x = Atom.expr (Atom.sym op :: args))
    (hcall : callGrounded (MinEnv.ofAtomsGT atoms gt).gt op
        (args.map (fun a => resolveStates St.init.world (subTokens St.init.world a))) =
      ReduceResult.noReduce)
    (hembed : isEmbeddedOp (Atom.expr (Atom.sym op :: args)) = false)
    (hsplit : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) =
      pre ++ (lhs, rhs) :: post)
    (hmatchCore : coreB ∈ matchAtoms lhs (Atom.expr (Atom.sym op :: args)))
    (hnotEmpty :
      (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
        (freshenRule (St.init.counter + pre.length) lhs rhs).2 != emptyA) = true)
    (hnotFunction :
      isFunctionResult
        (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2) = false) :
    instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
        (freshenRule (St.init.counter + pre.length) lhs rhs).2 ∈
        evalAtomMin (MinEnv.ofAtomsGT atoms gt) (fuel + 1) x ∧
      Relation.ReflTransGen (MopsStep atoms)
        (Atom.expr (Atom.sym op :: args)) (instantiate coreB rhs) ∧
      Metta.AlphaEq
        (instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2)
        (instantiate coreB rhs) := by
  rcases interpretFuel_eval_renamed_closed_coreBinding_reverse_alpha_final_mops_of_match
    (atoms := atoms) (gt := gt) (st := St.init) (fuel := fuel) (x := x)
    (lhs := lhs) (rhs := rhs) (coreB := coreB) (op := op) (args := args)
    (pre := pre) (post := post)
    hclosedTarget hclosedB hnodup rfl hinst hcall hembed hsplit hmatchCore
    hnotEmpty hnotFunction with
    ⟨hmem, hreach, halpha⟩
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr
      ⟨(instantiate (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse
          (freshenRule (St.init.counter + pre.length) lhs rhs).2,
        (renameBindings (counterSuffix (St.init.counter + pre.length)) coreB).reverse),
        by simpa [atomToStack_eval] using hmem, rfl⟩
  · exact ⟨hreach, halpha⟩

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
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp (List.mem_filter.mp hp).1 with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
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
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp (List.mem_filter.mp hp).1 with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted st it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
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
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
      | cons it rest =>
          simp only [interpretFuel] at hp
          rcases List.mem_append.mp (List.mem_filter.mp hp).1 with hdoneRev | hworkOut
          · exact hdone p (List.mem_reverse.mp hdoneRev)
          · rcases List.mem_map.mp hworkOut with ⟨it', hit', rfl⟩
            exact hExhausted st it' (hwork it' hit')
  | succ fuel ih =>
      intro st work done hdone hwork p hp
      cases work with
      | nil =>
          simp only [interpretFuel] at hp
          exact hdone p (List.mem_reverse.mp (List.mem_filter.mp hp).1)
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
    (hfinal : isFinal out = true)
    (hnotEmpty : ((finalPair out).1 != emptyA) = true) :
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
      simp [houtFinals, hnotEmpty]

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
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal (by
      simpa [out, finItem, finalPair, instantiate_notReducibleA] using notReducibleA_ne_empty)
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
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA,
    notReducibleA_ne_empty]

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
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal (by
      simpa [out, finItem, finalPair, instantiate_notReducibleA] using notReducibleA_ne_empty)
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
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA,
    notReducibleA_ne_empty]

/-- Fuel-driver harvest of
`interpretStack1_eval_ground_notReducible_of_no_candidates`. This is the executable root-evaluator
bridge for bare grounded normal forms such as Boolean control-flow leaves. -/
theorem interpretFuel_eval_ground_notReducible_of_no_candidates
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (g : Ground)
    (hinst : instantiate b x = Atom.gnd g)
    (hembed : isEmbeddedOp (Atom.gnd g) = false)
    (hnone : candidatesW env st.world (Atom.gnd g) = []) :
    (notReducibleA, b) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] []).1 := by
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }
  let out : Item := finItem [] notReducibleA b
  have hmem : out ∈ (interpretStack1 env fuel st it).1 := by
    simpa [it, out] using
      interpretStack1_eval_ground_notReducible_of_no_candidates env st fuel [] x b g
        hinst hembed hnone
  have hfinal : isFinal out = true := by
    simp [out, finItem, isFinal]
  have hharvest :=
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal (by
      simpa [out, finItem, finalPair, instantiate_notReducibleA] using notReducibleA_ne_empty)
  simpa [it, out, finItem, finalPair, instantiate_notReducibleA] using hharvest

/-- Exact fuel-driver form for bare-grounded no-candidate evaluation. -/
theorem interpretFuel_eval_ground_notReducible_of_no_candidates_eq
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (g : Ground)
    (hinst : instantiate b x = Atom.gnd g)
    (hembed : isEmbeddedOp (Atom.gnd g) = false)
    (hnone : candidatesW env st.world (Atom.gnd g) = []) :
    interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] [] =
      ([(notReducibleA, b)], st) := by
  have hstep := interpretStack1_eval_ground_notReducible_of_no_candidates_eq
    env st fuel [] x b g hinst hembed hnone
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA,
    notReducibleA_ne_empty]

/-- Fuel-driver harvest of `interpretStack1_eval_var_notReducible`. -/
theorem interpretFuel_eval_var_notReducible
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (v : VarName)
    (hinst : instantiate b x = Atom.var v)
    (hembed : isEmbeddedOp (Atom.var v) = false) :
    (notReducibleA, b) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] []).1 := by
  let it : Item := { stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }
  let out : Item := finItem [] notReducibleA b
  have hmem : out ∈ (interpretStack1 env fuel st it).1 := by
    simpa [it, out] using
      interpretStack1_eval_var_notReducible env st fuel [] x b v hinst hembed
  have hfinal : isFinal out = true := by
    simp [out, finItem, isFinal]
  have hharvest :=
    mem_interpretFuel_single_of_mem_interpretStack1_final env fuel st it out hmem hfinal (by
      simpa [out, finItem, finalPair, instantiate_notReducibleA] using notReducibleA_ne_empty)
  simpa [it, out, finItem, finalPair, instantiate_notReducibleA] using hharvest

/-- Exact fuel-driver form for bare-variable evaluation. -/
theorem interpretFuel_eval_var_notReducible_eq
    (env : MinEnv) (st : St) (fuel : Nat) (x : Atom) (b : Bindings) (v : VarName)
    (hinst : instantiate b x = Atom.var v)
    (hembed : isEmbeddedOp (Atom.var v) = false) :
    interpretFuel env (fuel + 1) st
        [{ stack := [{ atom := Atom.expr [Atom.sym "eval", x] }], bnd := b }] [] =
      ([(notReducibleA, b)], st) := by
  have hstep := interpretStack1_eval_var_notReducible_eq
    env st fuel [] x b v hinst hembed
  simp [interpretFuel, hstep, finItem, isFinal, finalPair, instantiate_notReducibleA,
    notReducibleA_ne_empty]

/-! ## Full `mettaEval` consumption of `NotReducible` root readouts -/

private def mettaEvalBareReturnPolicy (env : MinEnv) (world : World) (w : Atom) : Bool :=
  match selectFunctionType env world w [] with
  | .selected selected => returnsAtom selected
  | .exhausted _ _ => false

private def mettaEvalBareFoldStep (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (returnAtom : Bool) :
    List (Atom × Bindings) × St → Atom × Bindings → List (Atom × Bindings) × St :=
  fun a2 p =>
    if (p.1 == notReducibleA) = true ∨ (p.1 == w) = true then
      (a2.1 ++ [(w, bnd)], a2.2)
    else if returnAtom = true then
      (a2.1 ++ [p], a2.2)
    else
      (a2.1 ++ (mettaEval env fuel a2.2 p.2 p.1).1,
        (mettaEval env fuel a2.2 p.2 p.1).2)

private theorem mettaEvalBareFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (returnAtom : Bool)
    (p : Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (hmem : (w, bnd) ∈ acc.1) :
    (w, bnd) ∈ (mettaEvalBareFoldStep env fuel w bnd returnAtom acc p).1 := by
  unfold mettaEvalBareFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · split
    · exact List.mem_append.mpr (Or.inl hmem)
    · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalBareFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (returnAtom : Bool)
    (acc : List (Atom × Bindings) × St) :
    (w, bnd) ∈
      (mettaEvalBareFoldStep env fuel w bnd returnAtom acc (notReducibleA, bnd)).1 := by
  have hbeq : (notReducibleA == notReducibleA) = true := rfl
  unfold mettaEvalBareFoldStep
  simp [hbeq]

private theorem mettaEvalBareFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (returnAtom : Bool)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hmem : (w, bnd) ∈ acc.1) :
    (w, bnd) ∈
      (pairs.foldl (mettaEvalBareFoldStep env fuel w bnd returnAtom) acc).1 := by
  induction pairs generalizing acc with
  | nil => simpa using hmem
  | cons p ps ih =>
      exact ih _
        (mettaEvalBareFoldStep_preserves_mem env fuel w bnd returnAtom p acc hmem)

private theorem mettaEvalBareFold_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (w : Atom) (bnd : Bindings)
    (returnAtom : Bool)
    (pairs : List (Atom × Bindings)) (st : St)
    (hmem : (notReducibleA, bnd) ∈ pairs) :
    (w, bnd) ∈
      (pairs.foldl (mettaEvalBareFoldStep env fuel w bnd returnAtom) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  exact mettaEvalBareFold_preserves_mem env fuel w bnd returnAtom post _
    (mettaEvalBareFoldStep_hits_notReducible env fuel w bnd returnAtom _)

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
  simp [Metta.instantiate, Metta.Bindings.resolveAtom]
  cases hpairs : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.sym op]) [], bnd := bnd }] [] with
  | mk pairs st' =>
      simp only [hpairs] at hreadout ⊢
      change (Atom.sym op, bnd) ∈
        (pairs.foldl
          (mettaEvalBareFoldStep env fuel (Atom.sym op) bnd
            (mettaEvalBareReturnPolicy env st.world (Atom.sym op))) ([], st')).1
      exact mettaEvalBareFold_keeps_of_notReducible_readout env fuel (Atom.sym op) bnd
        (mettaEvalBareReturnPolicy env st.world (Atom.sym op)) pairs st' hreadout

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
  simp [Metta.instantiate, Metta.Bindings.resolveAtom]
  rw [hreadout]
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-- Full `mettaEval` keeps a bare grounded atom when the root minimal interpreter reports
`NotReducible`. This is the Boolean-control-flow sibling of
`mettaEval_symbol_keeps_of_notReducible_readout`. -/
theorem mettaEval_ground_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (g : Ground)
    (hreadout : (notReducibleA, bnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.gnd g]) [], bnd := bnd }] []).1) :
    (Atom.gnd g, bnd) ∈ (mettaEval env (fuel + 1) st bnd (Atom.gnd g)).1 := by
  unfold mettaEval
  simp [Metta.instantiate, Metta.Bindings.resolveAtom]
  cases hpairs : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.gnd g]) [], bnd := bnd }] [] with
  | mk pairs st' =>
      simp only [hpairs] at hreadout ⊢
      change (Atom.gnd g, bnd) ∈
        (pairs.foldl
          (mettaEvalBareFoldStep env fuel (Atom.gnd g) bnd
            (mettaEvalBareReturnPolicy env st.world (Atom.gnd g))) ([], st')).1
      exact mettaEvalBareFold_keeps_of_notReducible_readout env fuel (Atom.gnd g) bnd
        (mettaEvalBareReturnPolicy env st.world (Atom.gnd g)) pairs st' hreadout

/-- Exact version of `mettaEval_ground_keeps_of_notReducible_readout`. -/
theorem mettaEval_ground_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (g : Ground)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.gnd g]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.gnd g) = ([(Atom.gnd g, bnd)], st) := by
  unfold mettaEval
  simp [Metta.instantiate, Metta.Bindings.resolveAtom]
  rw [hreadout]
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-- Full `mettaEval` keeps a bare variable when the root minimal interpreter reports
`NotReducible`. -/
theorem mettaEval_var_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (v : VarName)
    (hinst : instantiate bnd (Atom.var v) = Atom.var v)
    (hreadout : (notReducibleA, bnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.var v]) [], bnd := bnd }] []).1) :
    (Atom.var v, bnd) ∈ (mettaEval env (fuel + 1) st bnd (Atom.var v)).1 := by
  unfold mettaEval
  rw [hinst]
  simp only
  cases hpairs : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.var v]) [], bnd := bnd }] [] with
  | mk pairs st' =>
      simp only [hpairs, Bool.or_eq_true] at hreadout ⊢
      change (Atom.var v, bnd) ∈
        (pairs.foldl
          (mettaEvalBareFoldStep env fuel (Atom.var v) bnd
            (mettaEvalBareReturnPolicy env st.world (Atom.var v))) ([], st')).1
      exact mettaEvalBareFold_keeps_of_notReducible_readout
        env fuel (Atom.var v) bnd
        (mettaEvalBareReturnPolicy env st.world (Atom.var v)) pairs st' hreadout

/-- Exact version of `mettaEval_var_keeps_of_notReducible_readout`. -/
theorem mettaEval_var_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (v : VarName)
    (hinst : instantiate bnd (Atom.var v) = Atom.var v)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.var v]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.var v) = ([(Atom.var v, bnd)], st) := by
  unfold mettaEval
  rw [hinst]
  simp only
  rw [hreadout]
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-- The inner fold used by `mettaEval` after evaluating a symbol-headed expression's arguments and
running the root `(eval w)` step.

Factoring it out lets corpus entries reason about the `NotReducible` case without re-expanding the
whole evaluator loop. -/
def mettaEvalExprRootFoldStep
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) :
    List (Atom × Bindings) × St → Atom × Bindings → List (Atom × Bindings) × St :=
  fun a2 p =>
    let pb := restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)
    if (p.1 == notReducibleA) = true ∨ (p.1 == w) = true then
      (a2.1 ++ [(w, partBnd)], a2.2)
    else if returnAtom = true then
      (a2.1 ++ [(p.1, pb)], a2.2)
    else
      let (more, st3) := mettaEval env fuel a2.2 pb p.1
      (a2.1 ++ more.map (fun m =>
        (m.1, restrictBnd queryVars ((Bindings.merge pb m.2).head?.getD m.2))), st3)

private theorem mettaEvalExprRootFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (p : Atom × Bindings)
    (acc : List (Atom × Bindings) × St)
    (hmem : (w, partBnd) ∈ acc.1) :
    (w, partBnd) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc p).1 := by
  unfold mettaEvalExprRootFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · split
    · exact List.mem_append.mpr (Or.inl hmem)
    · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalExprRootFoldStep_preserves_target_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (p : Atom × Bindings)
    (acc : List (Atom × Bindings) × St) {target : Atom × Bindings}
    (hmem : target ∈ acc.1) :
    target ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc p).1 := by
  unfold mettaEvalExprRootFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · split
    · exact List.mem_append.mpr (Or.inl hmem)
    · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalExprRootFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (acc : List (Atom × Bindings) × St)
    (rootBnd : Bindings) :
    (w, partBnd) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc
        (notReducibleA, rootBnd)).1 := by
  unfold mettaEvalExprRootFoldStep
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

private theorem mettaEvalExprRootFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hmem : (w, partBnd) ∈ acc.1) :
    (w, partBnd) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) acc).1 := by
  induction pairs generalizing acc with
  | nil => simpa using hmem
  | cons p ps ih =>
      exact ih _ (mettaEvalExprRootFoldStep_preserves_mem
        env fuel queryVars w partBnd returnAtom p acc hmem)

private theorem mettaEvalExprRootFold_preserves_target_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    {target : Atom × Bindings} (hmem : target ∈ acc.1) :
    target ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) acc).1 := by
  induction pairs generalizing acc with
  | nil => simpa using hmem
  | cons p ps ih =>
      exact ih _ (mettaEvalExprRootFoldStep_preserves_target_mem
        env fuel queryVars w partBnd returnAtom p acc hmem)

private theorem mettaEvalExprRootFoldStep_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (P : St → Prop)
    (hrec :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (p : Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc p).2 := by
  unfold mettaEvalExprRootFoldStep
  split
  · exact hacc
  · split
    · exact hacc
    · exact hrec acc p hacc

private theorem mettaEvalExprRootFold_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (P : St → Prop)
    (hrec :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (pairs : List (Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (pairs.foldl
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) acc).2 := by
  induction pairs generalizing acc with
  | nil => simpa using hacc
  | cons p ps ih =>
      exact ih _ (mettaEvalExprRootFoldStep_preserves_state_pred
        env fuel queryVars w partBnd returnAtom P hrec p acc hacc)

theorem mettaEval_expr_root_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (rootBnd : Bindings)
    (pairs : List (Atom × Bindings)) (st : St)
    (hmem : (notReducibleA, rootBnd) ∈ pairs) :
    (w, partBnd) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  exact mettaEvalExprRootFold_preserves_mem env fuel queryVars w partBnd returnAtom post _
    (mettaEvalExprRootFoldStep_hits_notReducible
      env fuel queryVars w partBnd returnAtom _ rootBnd)

/-- One root-fold step keeps an Atom-returning root readout. -/
private theorem mettaEvalExprRootFoldStep_hits_returnsAtom
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (acc : List (Atom × Bindings) × St)
    (p : Atom × Bindings)
    (hReturns : returnAtom = true)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false) :
    (p.1, restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc p).1 := by
  unfold mettaEvalExprRootFoldStep
  have hfirst :
      ¬ ((p.1 == notReducibleA) = true ∨ (p.1 == w) = true) := by
    intro h
    cases h with
    | inl hnr =>
        rw [hnotNR] at hnr
        cases hnr
    | inr hself =>
        rw [hnotSelf] at hself
        cases hself
  simp [hfirst, hReturns]

/-- The expression-root fold keeps any selected Atom-returning root readout.

This is the `returnsAtom` sibling of `mettaEval_expr_root_keeps_of_notReducible_readout`.
It is the right outer-loop fact for calls such as `nf`, whose declared result type is `Atom`:
the evaluator returns the root readout inert instead of recursively evaluating inside it. -/
theorem mettaEval_expr_root_keeps_of_returnsAtom_readout
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (p : Atom × Bindings) (pairs : List (Atom × Bindings)) (st : St)
    (hmem : p ∈ pairs)
    (hReturns : returnAtom = true)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false) :
    (p.1, restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  exact mettaEvalExprRootFold_preserves_target_mem
    env fuel queryVars w partBnd returnAtom post _
    (mettaEvalExprRootFoldStep_hits_returnsAtom
      env fuel queryVars w partBnd returnAtom _ p hReturns hnotNR hnotSelf)

/-- One root-fold step recursively evaluates a selected root readout. -/
private theorem mettaEvalExprRootFoldStep_hits_recursive_eval
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (acc : List (Atom × Bindings) × St)
    (p : Atom × Bindings) (final : Atom)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false)
    (hReturns : returnAtom = false)
    (hFinal : (final, []) ∈
      (mettaEval env fuel acc.2
        (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).1) :
    (final,
        restrictBnd queryVars
          (((restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom acc p).1 := by
  unfold mettaEvalExprRootFoldStep
  have hfirst : ¬ ((p.1 == notReducibleA) = true ∨ (p.1 == w) = true) := by
    intro h
    cases h with
    | inl hnr =>
        rw [hnotNR] at hnr
        cases hnr
    | inr hself =>
        rw [hnotSelf] at hself
        cases hself
  split
  · rename_i hbranch
    exact False.elim (hfirst hbranch)
  · split
    · rename_i hbranch
      have hret : returnAtom = true := hbranch
      rw [hReturns] at hret
      cases hret
    · exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨(final, []), hFinal, by simp⟩))

/-- The expression-root fold recursively evaluates any selected root readout.

The recursive premise is state-polymorphic because the selected readout may be processed after
earlier readouts have threaded the evaluator state. -/
theorem mettaEval_expr_root_evals_selected_readout_all_states
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (p : Atom × Bindings) (pairs : List (Atom × Bindings)) (st : St) (final : Atom)
    (hmem : p ∈ pairs)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).1) :
    (final,
        restrictBnd queryVars
          (((restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)
  have hhit :=
    mettaEvalExprRootFoldStep_hits_recursive_eval
      env fuel queryVars w partBnd returnAtom accPre p final hnotNR hnotSelf hReturns
      (hFinal accPre.2)
  exact mettaEvalExprRootFold_preserves_target_mem
    env fuel queryVars w partBnd returnAtom post _ hhit

/-- State-invariant version of `mettaEval_expr_root_evals_selected_readout_all_states`.

Earlier root readouts may thread the evaluator state before the selected readout is processed.
When a recursive readout theorem is valid only under a state invariant (for example, no local
world rules), this lemma carries that invariant through the prefix of the fold and uses it at the
selected readout. -/
theorem mettaEval_expr_root_evals_selected_readout_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool) (P : St → Prop)
    (p : Atom × Bindings) (pairs : List (Atom × Bindings)) (st : St) (final : Atom)
    (hmem : p ∈ pairs)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false)
    (hReturns : returnAtom = false)
    (hinit : P st)
    (hstep :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (hFinal : ∀ st0,
      P st0 →
        (final, []) ∈
          (mettaEval env fuel st0
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).1) :
    (final,
        restrictBnd queryVars
          (((restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)
  have hpre : P accPre.2 := by
    exact mettaEvalExprRootFold_preserves_state_pred
      env fuel queryVars w partBnd returnAtom P hstep pre ([], st) hinit
  have hhit :=
    mettaEvalExprRootFoldStep_hits_recursive_eval
      env fuel queryVars w partBnd returnAtom accPre p final hnotNR hnotSelf hReturns
      (hFinal accPre.2 hpre)
  exact mettaEvalExprRootFold_preserves_target_mem
    env fuel queryVars w partBnd returnAtom post _ hhit

/-- Exact singleton form of the expression-root fold's `NotReducible` case. -/
theorem mettaEvalExprRootFold_eq_of_notReducible_singleton
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (rootBnd : Bindings) (st : St) :
    List.foldl (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom) ([], st)
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
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool) :
    List (Atom × Bindings) × St → List Atom × Bindings → List (Atom × Bindings) × St :=
  fun acc part =>
    match (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) with
    | some (err, _) => (acc.1 ++ [(err, part.2)], acc.2)
    | none =>
        let w := Atom.expr (Atom.sym op :: part.1)
        let (pairs, st') := interpretFuel env (fuel + 1) acc.2
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", w]) [], bnd := bnd }] []
        let (out, st'') := pairs.foldl
          (mettaEvalExprRootFoldStep env fuel queryVars w part.2 returnAtom) ([], st')
        (acc.1 ++ out, st'')

private theorem mettaEvalExprPartFoldStep_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (part : List Atom × Bindings) (acc : List (Atom × Bindings) × St)
    {target : Atom × Bindings}
    (hmem : target ∈ acc.1) :
    target ∈
      (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom acc part).1 := by
  unfold mettaEvalExprPartFoldStep
  split
  · exact List.mem_append.mpr (Or.inl hmem)
  · exact List.mem_append.mpr (Or.inl hmem)

private theorem mettaEvalExprPartFold_preserves_mem
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (parts : List (List Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    {target : Atom × Bindings}
    (hmem : target ∈ acc.1) :
    target ∈
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) acc).1 := by
  induction parts generalizing acc with
  | nil => simpa using hmem
  | cons part parts ih =>
      exact ih _ (mettaEvalExprPartFoldStep_preserves_mem
        env fuel queryVars op args bnd returnAtom part acc hmem)

private theorem mettaEvalExprPartFold_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (P : St → Prop)
    (hstep :
      ∀ (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings),
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom acc part).2)
    (parts : List (List Atom × Bindings)) (acc : List (Atom × Bindings) × St)
    (hacc : P acc.2) :
    P (parts.foldl
      (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) acc).2 := by
  induction parts generalizing acc with
  | nil => simpa using hacc
  | cons part parts ih =>
      exact ih _ (hstep acc part hacc)

private theorem mettaEvalExprPartFoldStep_preserves_state_pred_of_root
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
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
    P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom acc part).2 := by
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
                  (Atom.expr (Atom.sym op :: part.1)) part.2 returnAtom)
                ([], st') pairs).2 :=
          mettaEvalExprRootFold_preserves_state_pred env fuel queryVars
            (Atom.expr (Atom.sym op :: part.1)) part.2 returnAtom P
            (fun acc p hP => hrec part.2 acc p hP)
            pairs ([], st') hrootState
        simpa [hpairs] using hfold

private theorem mettaEvalExprPartFoldStep_hits_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (part : List Atom × Bindings) (acc : List (Atom × Bindings) × St)
    (rootBnd : Bindings)
    (hnoerr : (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none)
    (hroot : (notReducibleA, rootBnd) ∈
      (interpretFuel env (fuel + 1) acc.2
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
            Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).1) :
    (Atom.expr (Atom.sym op :: part.1), part.2) ∈
      (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom acc part).1 := by
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
              env fuel queryVars (Atom.expr (Atom.sym op :: part.1)) part.2 returnAtom rootBnd
              pairs st' hrootPairs)))

theorem mettaEvalExprPartFold_keeps_of_part_notReducible
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
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
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init).1 := by
  rcases List.mem_iff_append.mp hpart with ⟨pre, post, hparts⟩
  rw [hparts, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init
  have hhit :=
    mettaEvalExprPartFoldStep_hits_notReducible
      env fuel queryVars op args bnd returnAtom part accPre rootBnd hnoerr (hroot accPre)
  exact mettaEvalExprPartFold_preserves_mem
    env fuel queryVars op args bnd returnAtom post _ hhit

/-- Invariant-aware form of `mettaEvalExprPartFold_keeps_of_part_notReducible`.

The selected partial may be processed after earlier partials have threaded the evaluator state.
Callers provide a state predicate `P`, a proof that the part fold preserves it, and a root readout
premise under `P`. This is the shape needed by the static-fragment runtime-correctness bridge:
the selected root step does not need to work for arbitrary states, only for states satisfying the
fragment invariant. -/
theorem mettaEvalExprPartFold_keeps_of_part_notReducible_of_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (P : St → Prop)
    (parts : List (List Atom × Bindings)) (init : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) (rootBnd : Bindings)
    (hinit : P init.2)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom acc part).2)
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
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init).1 := by
  rcases List.mem_iff_append.mp hpart with ⟨pre, post, hparts⟩
  rw [hparts, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init
  have haccPre : P accPre.2 :=
    mettaEvalExprPartFold_preserves_state_pred env fuel queryVars op args bnd returnAtom P
      hstep pre init hinit
  have hhit :=
    mettaEvalExprPartFoldStep_hits_notReducible
      env fuel queryVars op args bnd returnAtom part accPre rootBnd hnoerr
      (hroot accPre haccPre)
  exact mettaEvalExprPartFold_preserves_mem
    env fuel queryVars op args bnd returnAtom post _ hhit

/-- Invariant-aware selected-readout form of the expression-part fold.

This is the part-fold analogue of
`mettaEval_expr_root_evals_selected_readout_state_pred`: once one selected
partial application has been chosen, the theorem carries a state invariant
through the prefix of the part fold, through the selected root `interpretFuel`
step, and through the selected recursive `mettaEval` call on the resulting root
readout.  It is the reusable scheduler fact behind control operators such as
stdlib `let` and `if`, where the evaluated argument may have many readouts but a
later proof wants to follow one concrete branch honestly. -/
theorem mettaEvalExprPartFold_evals_selected_readout_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (P : St → Prop)
    (parts : List (List Atom × Bindings)) (init : List (Atom × Bindings) × St)
    (part : List Atom × Bindings)
    (p : Atom × Bindings) (final : Atom)
    (hinit : P init.2)
    (hpart : part ∈ parts)
    (hnoerr : (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none)
    (hrootState :
      ∀ (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings),
        P acc.2 →
          P (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).2)
    (hrecState :
      ∀ (partBnd : Bindings)
        (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd queryVars ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).2)
    (hroot :
      ∀ acc : List (Atom × Bindings) × St,
        P acc.2 →
          p ∈
            (interpretFuel env (fuel + 1) acc.2
              [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                  Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] []).1)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == Atom.expr (Atom.sym op :: part.1)) = false)
    (hReturns : returnAtom = false)
    (hFinal :
      ∀ st0,
        P st0 →
          (final, []) ∈
            (mettaEval env fuel st0
              (restrictBnd queryVars ((Bindings.merge part.2 p.2).head?.getD p.2)) p.1).1) :
    (final,
        restrictBnd queryVars
          (((restrictBnd queryVars ((Bindings.merge part.2 p.2).head?.getD p.2)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init).1 := by
  rcases List.mem_iff_append.mp hpart with ⟨pre, post, hparts⟩
  rw [hparts, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl (mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom) init
  have haccPre : P accPre.2 := by
    exact mettaEvalExprPartFold_preserves_state_pred
      env fuel queryVars op args bnd returnAtom P
      (fun acc part hP =>
        mettaEvalExprPartFoldStep_preserves_state_pred_of_root
          env fuel queryVars op args bnd returnAtom P hrootState hrecState acc part hP)
      pre init hinit
  have hhit :
      (final,
          restrictBnd queryVars
            (((restrictBnd queryVars ((Bindings.merge part.2 p.2).head?.getD p.2)).merge
                ([] : Bindings)).head?.getD [])) ∈
        (mettaEvalExprPartFoldStep
          env fuel queryVars op args bnd returnAtom accPre part).1 := by
    unfold mettaEvalExprPartFoldStep
    rw [hnoerr]
    simp only
    cases hpairs : interpretFuel env (fuel + 1) accPre.2
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
            Atom.expr (Atom.sym op :: part.1)]) [], bnd := bnd }] [] with
    | mk pairs st' =>
        have hrootPairs : p ∈ pairs := by
          have hrootMem := hroot accPre haccPre
          rw [hpairs] at hrootMem
          simpa using hrootMem
        have hstate' : P st' := by
          have hrootState' := hrootState accPre part haccPre
          rw [hpairs] at hrootState'
          simpa using hrootState'
        have hfold :=
          mettaEval_expr_root_evals_selected_readout_state_pred
            env fuel queryVars (Atom.expr (Atom.sym op :: part.1)) part.2 returnAtom P
            p pairs st' final hrootPairs hnotNR hnotSelf hReturns
            hstate'
            (fun acc p hP => hrecState part.2 acc p hP)
            (by
              intro st0 hP
              simpa using hFinal st0 hP)
        exact List.mem_append.mpr (Or.inr hfold)
  exact mettaEvalExprPartFold_preserves_mem
    env fuel queryVars op args bnd returnAtom post _ hhit

/-- The singleton work item used by the minimal interpreter to evaluate `a` with empty bindings. -/
def evalItemNil (a : Atom) : Item :=
  { stack := atomToStack (Atom.expr [Atom.sym "eval", a]) [] }

/-- Exact non-error control policy for one symbol-headed application.

The policy is intentionally partial.  It represents either one signature selected by the ordered
type scan, or the zero-candidate, zero-error tuple fallback.  Error-emitting exhaustion and
non-tuple exhaustion have no constructor, so a theorem consuming this policy cannot silently drop
runtime error results.  The indices force the argument mask and return policy to be the projections
of the same selection decision. -/
inductive ExactApplicationPolicy (env : MinEnv) (world : World) (op : String)
    (args : List Atom) : List Bool → Bool → Prop where
  | selected (selected : SelectedFunctionType)
      (hSelected : selectFunctionType env world (.sym op) args = .selected selected) :
      ExactApplicationPolicy env world op args
        (argMask selected args.length) (returnsAtom selected)
  | untypedTuple
      (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true) :
      ExactApplicationPolicy env world op args (List.replicate args.length true) false

/-- A non-error application policy exposes exactly the evaluator branch selected at runtime.

The recursive evaluator and reducer below are the literal callbacks used by `mettaEval`; this
equation is the single proof boundary shared by selected signatures and untyped tuple fallback. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool)
    (hPolicy : ExactApplicationPolicy env st.world op args mask returnAtom) :
    mettaEval env (fuel + 1) st [] (Atom.expr (Atom.sym op :: args)) =
      evaluateSelectedApplication
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := [] }] [])
        st op args mask returnAtom := by
  conv_lhs => unfold mettaEval
  rw [instantiate_nil (Atom.expr (Atom.sym op :: args))]
  simp only
  cases hPolicy with
  | selected selected hSelected =>
      rw [hSelected]
  | untypedTuple hScan =>
      rw [hScan]
      simp

/-- The exact application-policy boundary after an incoming binding has instantiated the source
application.  Unlike the empty-binding specialization above, the reducer retains the incoming
binding on its root work item, exactly as `mettaEval` does. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactPolicy_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom) (mask : List Bool) (returnAtom : Bool)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hPolicy : ExactApplicationPolicy env st.world op args mask returnAtom) :
    mettaEval env (fuel + 1) st bnd source =
      evaluateSelectedApplication
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bnd }] [])
        st op args mask returnAtom := by
  conv_lhs => unfold mettaEval
  rw [hInstantiate]
  simp only
  cases hPolicy with
  | selected selected hSelected =>
      rw [hSelected]
  | untypedTuple hScan =>
      rw [hScan]
      simp

/-- One-argument constructor congruence for the executable `mettaEval` loop.

If the single argument of `(op arg)` evaluates to one readout `out`, and the rebuilt root
`(op out)` reports `NotReducible`, then the full evaluator keeps `(op out)`. This is the generic
outer-loop lemma needed by Peano-style constructors before proving a full evaluator computation
theorem; it avoids tracing one constructor layer at a time. -/
theorem mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : ExactApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : out.isError = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] mask returnAtom hPolicy]
  simp [evaluateSelectedApplication, hMask, hArg, hNotError]
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
            (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
            returnAtom)
          ([], stRoot) pairs).1
      exact
        mettaEval_expr_root_keeps_of_notReducible_readout
          env fuel (arg.vars) (Atom.expr [Atom.sym op, out])
          (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
          returnAtom [] pairs stRoot hrootPairs

/-- Selected-signature specialization of
`mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy`. -/
theorem mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
    (hNotError : out.isError = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  exact mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    env fuel st stArg op arg out (argMask selected 1) (returnsAtom selected)
    hArg (.selected selected hSelected) hMask hNotError hroot

/-- Membership-side soundness package for the unary constructor fold.

This is the non-exact counterpart of
`mettaEval_unary_expr_singleton_sound_of_arg_singleton_and_notReducible_eq`: it keeps the root
minimal-interpreter result as a membership premise and returns the actual outer readout together
with the caller-supplied certified relation chain under the constructor. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : ExactApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
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
      mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy
        env fuel st stArg op arg out mask returnAtom hArg hPolicy hMask hNotError hroot
  · exact hReach

/-- Selected-signature specialization of the unary singleton relation package. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
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
  exact mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    env fuel st stArg op arg out (argMask selected 1) (returnsAtom selected) R
    hArg (.selected selected hSelected) hMask hNotError hroot hReach

/-- Unary constructor readout from a selected argument readout.

Unlike the singleton package above, this theorem allows the argument evaluator to return many
readouts.  The selected readout is followed through the argument-fold into the root-fold.  The root
`NotReducible` premise is quantified over every threaded state because earlier partials in the same
fold may have advanced the evaluator state before the selected partial is processed. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
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
  simp only
  rw [hSelected]
  simp only
  simp [evaluateSelectedApplication, hMask]
  rw [hArg]
  simp
  change (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
    (parts.foldl
      (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [] (returnsAtom selected))
      ([], stArg)).1
  have hkeep := mettaEvalExprPartFold_keeps_of_part_notReducible
    env fuel arg.vars op [arg] [] (returnsAtom selected) parts ([], stArg) part []
    hpart hnoerr hrootPart
  simpa [part] using hkeep

/-- Invariant-aware selected-readout unary constructor theorem.

This is the preferred version for the static symbol-headed fragment. Earlier partials in the
argument/result fold may thread the evaluator state before the selected partial is processed, so
the root readout premise is stated under a state predicate `P`, together with a proof that the part
fold preserves `P`. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (mask : List Bool) (returnAtom : Bool)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hPolicy : ExactApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] []
            returnAtom acc part).2)
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
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] mask returnAtom hPolicy]
  simp [evaluateSelectedApplication, hMask]
  rw [hArg]
  simp
  change (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
    (parts.foldl
      (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] [] returnAtom)
      ([], stArg)).1
  have hkeep := mettaEvalExprPartFold_keeps_of_part_notReducible_of_state_pred
    env fuel arg.vars op [arg] [] returnAtom P parts ([], stArg) part []
    hinit hstep hpart hnoerr hrootPart
  simpa [part] using hkeep

/-- Selected-signature specialization of the invariant-aware unary policy theorem. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] []
            (returnsAtom selected) acc part).2)
    (hroot :
      ∀ st0 : St,
        P st0 →
          (notReducibleA, []) ∈
            (interpretFuel env (fuel + 1) st0
              [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  exact mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred_of_exactPolicy
    env fuel st stArg op arg out argPairs (argMask selected 1) (returnsAtom selected) P
    hArg hmemArg (.selected selected hSelected) hMask hNotError hinit hstep hroot

/-- Relation-sound package for the selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
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
        env fuel st stArg op arg out argPairs selected hArg hmemArg hSelected hMask
        hNotError hroot
  · exact hReach

/-- Relation-sound package for the invariant-aware selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (mask : List Bool) (returnAtom : Bool)
    (P : St → Prop) (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hPolicy : ExactApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] []
            returnAtom acc part).2)
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
      mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_state_pred_of_exactPolicy
        env fuel st stArg op arg out argPairs mask returnAtom P hArg hmemArg hPolicy hMask
        hNotError hinit hstep hroot
  · exact hReach

/-- Selected-signature specialization of the invariant-aware unary relation package. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (P : St → Prop) (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
    (hNotError : out.isError = false)
    (hinit : P stArg)
    (hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep env fuel arg.vars op [arg] []
            (returnsAtom selected) acc part).2)
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
  exact mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred_of_exactPolicy
    env fuel st stArg op arg out argPairs (argMask selected 1) (returnsAtom selected) P R
    hArg hmemArg (.selected selected hSelected) hMask hNotError hinit hstep hroot hReach

/-- Exact one-argument constructor congruence for the executable `mettaEval` loop.

This is still a one-layer theorem: callers provide the argument evaluator result and the rebuilt
root evaluator result. It is useful for inductive proofs, but it does not encode any concrete Peano
fuel arithmetic. -/
theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : ExactApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : out.isError = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] mask returnAtom hPolicy]
  simp [evaluateSelectedApplication, hMask, hArg, hNotError]
  have hrootDirect :
      interpretFuel env (fuel + 1) stArg
        [({ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [] } :
          Item)] [] = ([(notReducibleA, [])], stRoot) := by
    simpa [evalItemNil] using hroot
  rw [hrootDirect]
  change
    List.foldl
        (mettaEvalExprRootFoldStep env fuel arg.vars (Atom.expr [Atom.sym op, out])
          (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
          returnAtom)
        ([], stRoot) [(notReducibleA, [])] =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot)
  exact mettaEvalExprRootFold_eq_of_notReducible_singleton
    env fuel arg.vars (Atom.expr [Atom.sym op, out])
    (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
    returnAtom [] stRoot

/-- Selected-signature specialization of the exact unary policy theorem. -/
theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (arg out : Atom) (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
    (hNotError : out.isError = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  exact mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy
    env fuel st stArg stRoot op arg out (argMask selected 1) (returnsAtom selected)
    hArg (.selected selected hSelected) hMask hNotError hroot

/-! ## Closed binary expression fold -/

/-- Closed two-argument outer-loop fold for the executable `mettaEval` evaluator.

This is the generic evaluator plumbing behind closed binary applications in the static fragment.
Callers provide:
* the actual evaluator results for both arguments;
* the root minimal-interpreter readout for the rebuilt application; and
* the recursive evaluation of that root readout.

The closed-argument hypotheses keep query-variable binding retention out of this theorem, which is
the first reusable binary fold needed by verified-MeTTa examples and SR-style kernel rules. -/
theorem mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hPolicy : ExactApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnAtom = false)
    (hFinal : mettaEval env fuel stRoot [] root = ([(final, [])], stOut)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(final, [])], stOut) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x, y] mask returnAtom hPolicy]
  simp only [evaluateSelectedApplication, hMask, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
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

/-- Selected-signature specialization of the exact closed-binary policy theorem. -/
theorem mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : mettaEval env fuel stRoot [] root = ([(final, [])], stOut)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(final, [])], stOut) := by
  exact mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval_of_exactPolicy
    env fuel st st₁ st₂ stRoot stOut op x y x' y' root final rootBnd
    (argMask selected 2) (returnsAtom selected) hxClosed hyClosed hx hy
    (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal

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
theorem mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hPolicy : ExactApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnAtom = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x, y] mask returnAtom hPolicy]
  simp only [evaluateSelectedApplication, hMask, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
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

/-- Selected-signature specialization of the membership-shaped binary policy theorem. -/
theorem mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 := by
  exact mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem_of_exactPolicy
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
    (argMask selected 2) (returnsAtom selected) hxClosed hyClosed hx hy
    (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal

/-- Closed binary expression fold when the root minimal interpreter reports
`NotReducible`.

After both closed arguments evaluate to singleton empty-binding readouts, a
root `NotReducible` result means the full `mettaEval` loop keeps the evaluated
expression itself.  This is the binary counterpart of the unary/part-fold
`NotReducible` plumbing used by the verified examples. -/
theorem mettaEval_binary_expr_eq_of_arg_singletons_and_root_notReducible
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find?
      (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(Atom.expr [Atom.sym op, x', y'], [])], stRoot) := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x, y])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hx]
  simp [hxClosed, hyClosed, restrictBnd_nil_vars]
  rw [hy]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  have hRoot' :
      interpretFuel env (fuel + 1) st₂
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, x', y']]) [], bnd := [] }] [] =
      ([(notReducibleA, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-- Closed binary expression fold through the ordered scan's tuple fallback.

An untyped operator has no arrow candidate, so the exact scan reports an empty error list and
tuple eligibility.  The evaluator then evaluates every argument and reduces the rebuilt expression
with return policy `false`.  Keeping this case separate from selected signatures prevents proofs
from fabricating a `SelectedFunctionType` for an untyped tuple. -/
theorem mettaEval_binary_expr_eq_of_tuple_fallback_and_root_notReducible
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' : Atom) (rootBnd : Bindings)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hScan : selectFunctionType env st.world (.sym op) [x, y] = .exhausted [] true)
    (hNoErr : (([x', y'].zip [x, y]).find?
      (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(Atom.expr [Atom.sym op, x', y'], [])], stRoot) := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x, y])]
  simp only
  rw [hScan]
  simp only [evaluateSelectedApplication, List.replicate_succ, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.zip_cons_cons,
    List.foldl_cons, List.foldl_nil, List.map_nil, List.nil_append]
  rw [hx]
  simp [hxClosed, hyClosed, restrictBnd_nil_vars]
  rw [hy]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  have hRoot' :
      interpretFuel env (fuel + 1) st₂
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, x', y']]) [], bnd := [] }] [] =
      ([(notReducibleA, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  have hnr : (notReducibleA == notReducibleA) = true := rfl
  simp [hnr]

/-! ## Closed quaternary expression fold -/

/-- Four-argument expression fold where all argument evaluators return empty bindings, but the
arguments themselves may contain query variables.

The existing closed-argument fold is enough for ordinary data constructors.  Embedded control
operators such as `(unify atom (Bad $e) then else)` deliberately contain an open pattern argument;
when each argument nevertheless evaluates to a singleton with empty bindings and the root readout
also carries empty bindings, the same executable fold is valid. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom)
    (mask : List Bool) (returnAtom : Bool)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hPolicy : ExactApplicationPolicy env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, []) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy]
  simp only [evaluateSelectedApplication, hMask,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hw]
  simp [restrictBnd_empty_merge_empty]
  rw [hx]
  simp [restrictBnd_empty_merge_empty]
  rw [hy]
  simp [restrictBnd_empty_merge_empty]
  rw [hz]
  simp [restrictBnd_empty_merge_empty]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(w', w), (x', x), (y', y), (z', z)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, w', x', y', z']]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st₄ [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, []) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, w', x', y', z']) [] returnAtom
          (root, []) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [restrictBnd_empty_merge_empty] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, w', x', y', z']) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, w', x', y', z'], [])], a2.2)
          else if returnAtom = true then
            (a2.1 ++
              [(p.1,
                restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                    ((Bindings.merge [] p.2).head?.getD p.2)) p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                        ((Bindings.merge
                          (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                            ((Bindings.merge [] p.2).head?.getD p.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, w', x', y', z']) [] returnAtom by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [restrictBnd_empty_merge_empty, qvars] using hfold

/-- Selected-signature specialization of the quaternary empty-root policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom)
    (selected : SelectedFunctionType)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, []) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ st₃ st₄ op w x y z w' x' y' z' root final
    (argMask selected 4) (returnsAtom selected) hw hx hy hz
    (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal

/-- Membership-shaped four-argument expression fold for an open root readout.

This is the binding-carrying sibling of
`mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member`.
It is needed for embedded `unify` success: the root `unify` frame returns a
readout together with a matcher binding, and the outer expression fold must
thread exactly the binding restricted to the original query variables.  The
theorem stays generic in the operator and selected root readout; it does not
unfold a concrete control-flow trace. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_open_root_eval_member_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hPolicy : ExactApplicationPolicy env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([w, x, y, z]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy]
  simp only [evaluateSelectedApplication, hMask,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hw]
  simp [restrictBnd_empty_merge_empty]
  rw [hx]
  simp [restrictBnd_empty_merge_empty]
  rw [hy]
  simp [restrictBnd_empty_merge_empty]
  rw [hz]
  simp [restrictBnd_empty_merge_empty]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(w', w), (x', x), (y', y), (z', z)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, w', x', y', z']]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st₄ [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, w', x', y', z']) [] returnAtom
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, w', x', y', z']) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, w', x', y', z'], [])], a2.2)
          else if returnAtom = true then
            (a2.1 ++
              [(p.1,
                restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                    ((Bindings.merge [] p.2).head?.getD p.2)) p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                        ((Bindings.merge
                          (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                            ((Bindings.merge [] p.2).head?.getD p.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, w', x', y', z']) [] returnAtom by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [qvars] using hfold

/-- Selected-signature specialization of the quaternary open-root policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([w, x, y, z]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact mettaEval_quaternary_expr_mem_of_arg_singletons_and_open_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ st₃ st₄ op w x y z w' x' y' z' root final rootBnd
    (argMask selected 4) (returnsAtom selected) hw hx hy hz
    (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal

/-- Membership-shaped four-argument expression fold for quoted arguments.

This is the executable scheduler shape for prelude operators whose signatures
mark all four arguments as `Atom`-like data, such as stdlib `unify`: the outer
`mettaEval` loop quotes all arguments, reduces the rebuilt root expression, and
then recursively evaluates the selected root readout.  Callers still supply the
operator's exact selected-signature witness, mask, and return policy rather
than forcing this generic theorem to unfold a large environment. -/
theorem mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String)
    (w x y z root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hPolicy : ExactApplicationPolicy env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [false, false, false, false])
    (hNoErr :
      (([w, x, y, z].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, w, x, y, z])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w, x, y, z]) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([w, x, y, z]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy]
  simp only [evaluateSelectedApplication, hMask, List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(w, w), (x, x), (y, y), (z, z)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, w, x, y, z]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, w, x, y, z])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, w, x, y, z]) [] returnAtom
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, w, x, y, z]) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, w, x, y, z], [])], a2.2)
          else if returnAtom = true then
            (a2.1 ++
              [(p.1,
                restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                    ((Bindings.merge [] p.2).head?.getD p.2)) p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                        ((Bindings.merge
                          (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                            ((Bindings.merge [] p.2).head?.getD p.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (w.vars ++ (x.vars ++ (y.vars ++ z.vars)))
                  ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, w, x, y, z]) [] returnAtom by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [qvars] using hfold

/-- Selected-signature specialization of the quoted quaternary policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String)
    (w x y z root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hMask : argMask selected 4 = [false, false, false, false])
    (hNoErr :
      (([w, x, y, z].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, w, x, y, z])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w, x, y, z]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([w, x, y, z]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact
    mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member_of_exactPolicy
      env fuel st op w x y z root final rootBnd
      (argMask selected 4) (returnsAtom selected)
      (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible
      hRootNotSelf hReturns hFinal

/-- Membership-shaped ternary expression fold for quoted arguments.

This is the arity-three sibling of
`mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member`: the
outer `mettaEval` loop quotes all three arguments according to the runtime
signature, reduces the rebuilt root expression once, and then recursively
evaluates the selected root readout.  Callers still provide the operator's
concrete signature facts rather than forcing this scheduler lemma to unfold a
large environment. -/
theorem mettaEval_ternary_expr_mem_of_quoted_args_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String)
    (x y z root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [x, y, z] = .selected selected)
    (hMask : argMask selected 3 = [false, false, false])
    (hNoErr :
      (([x, y, z].zip [x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, x, y, z])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x, y, z]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([x, y, z]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y, z])).1 := by
  let qvars := ([x, y, z]).flatMap Atom.vars
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x, y, z])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(x, x), (y, y), (z, z)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, x, y, z]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, x, y, z])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, x, y, z]) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, x, y, z]) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, x, y, z], [])], a2.2)
          else if returnsAtom selected = true then
            (a2.1 ++
              [(p.1,
                restrictBnd (x.vars ++ (y.vars ++ z.vars))
                  ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (x.vars ++ (y.vars ++ z.vars))
                    ((Bindings.merge [] p.2).head?.getD p.2)) p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (x.vars ++ (y.vars ++ z.vars))
                        ((Bindings.merge
                          (restrictBnd (x.vars ++ (y.vars ++ z.vars))
                            ((Bindings.merge [] p.2).head?.getD p.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (x.vars ++ (y.vars ++ z.vars))
                  ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, x, y, z]) [] (returnsAtom selected) by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [qvars] using hfold

/-- Membership-shaped one-argument expression fold for quoted arguments.

This is the executable scheduler shape for unary prelude operators whose signatures quote their
sole argument as data, reduce the rebuilt root expression, and then recursively evaluate the
selected root readout.  It is the unary companion to
`mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member`; callers provide the
operator's concrete signature and root-step facts. -/
theorem mettaEval_unary_expr_mem_of_quoted_arg_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String)
    (x root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [x] = .selected selected)
    (hMask : argMask selected 1 = [false])
    (hNoErr :
      (([x].zip [x]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, x])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd x.vars ((Bindings.merge [] rootBnd).head?.getD rootBnd))
          root).1) :
    (final,
        restrictBnd x.vars
          (((restrictBnd x.vars ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x])).1 := by
  let qvars := x.vars
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, x])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(x, x)] = none := by
    simpa using hNoErr
  have hNoErrIf :
      (if x.isError = true ∧ (x != x) = true then some (x, x) else none) = none := by
    cases hx : x.isError <;> cases hxx : (x != x) <;>
      simp [hx, hxx] at hNoErr' ⊢
  rw [hNoErrIf]
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, x]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, x])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, x]) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, x]) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, x], [])], a2.2)
          else if returnsAtom selected = true then
            (a2.1 ++
              [(p.1,
                restrictBnd x.vars ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd x.vars ((Bindings.merge [] p.2).head?.getD p.2))
                  p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd x.vars
                        ((Bindings.merge
                          (restrictBnd x.vars ((Bindings.merge [] p.2).head?.getD p.2))
                          m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd x.vars ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, x]) [] (returnsAtom selected) by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [qvars] using hfold

/-- Membership-shaped ternary expression fold for a quoted/evaluated/quoted argument mask.

This is the executable scheduler shape of stdlib `let`: `let` quotes the
pattern, evaluates the bound atom, quotes the template, then reduces the rebuilt
root expression.  The theorem is generic in the operator and environment;
callers provide one exact selected-signature witness and its mask.  It is the
`kernelEnv` control-flow companion to the all-arguments-evaluated quaternary
folds above, and avoids re-expanding a concrete `convReadout` trace. -/
theorem mettaEval_ternary_expr_mem_of_quoted_eval_quoted_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String)
    (p atom templ atom' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] atom = ([(atom', [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [p, atom, templ] = .selected selected)
    (hMask : argMask selected 3 = [false, true, false])
    (hNoErr :
      (([p, atom', templ].zip [p, atom, templ]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, p, atom', templ])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, p, atom', templ]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([p, atom, templ]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([p, atom, templ]).flatMap Atom.vars)
          (((restrictBnd (([p, atom, templ]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, p, atom, templ])).1 := by
  let qvars := p.vars ++ (atom.vars ++ templ.vars)
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, p, atom, templ])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  rw [hArg]
  simp [restrictBnd_empty_merge_empty]
  rw [Metta.instantiate_nil templ]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(p, p), (atom', atom), (templ, templ)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, p, atom', templ]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) stArg [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, p, atom', templ])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, p, atom', templ]) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p2 =>
          if (p2.1 == notReducibleA) = true ∨
              (p2.1 == Atom.expr [Atom.sym op, p, atom', templ]) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, p, atom', templ], [])], a2.2)
          else if returnsAtom selected = true then
            (a2.1 ++
              [(p2.1,
                restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                  ((Bindings.merge [] p2.2).head?.getD p2.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                    ((Bindings.merge [] p2.2).head?.getD p2.2)) p2.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                        ((Bindings.merge
                          (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                            ((Bindings.merge [] p2.2).head?.getD p2.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                  ((Bindings.merge [] p2.2).head?.getD p2.2)) p2.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, p, atom', templ]) [] (returnsAtom selected) by
        funext a2 p2
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [restrictBnd_empty_merge_empty, qvars] using hfold

/-- Membership-shaped ternary expression fold for a quoted/evaluated/quoted argument mask,
following one selected evaluated-argument readout with empty bindings under a
state invariant.

This is the variant needed by static fragments such as `nf`: the evaluated
middle argument may return many readouts, but the selected runtime readout
itself carries no query bindings.  The theorem follows that one readout through
the template-appending part fold and then through the selected root readout
under a state predicate `P`. -/
theorem mettaEval_ternary_expr_mem_of_quoted_eval_quoted_and_root_eval_member_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String)
    (p atom templ atom' root final : Atom) (argPairs : List (Atom × Bindings))
    (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] atom = (argPairs, stArg))
    (hmemArg : (atom', []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [p, atom, templ] = .selected selected)
    (hMask : argMask selected 3 = [false, true, false])
    (hNoErr :
      (([p, atom', templ].zip [p, atom, templ]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hinit : P stArg)
    (hrootState :
      ∀ (acc : List (Atom × Bindings) × St) (part : List Atom × Bindings),
        P acc.2 →
          P (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).2)
    (hrecState :
      ∀ (partBnd : Bindings)
        (acc : List (Atom × Bindings) × St) (p' : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd (([p, atom, templ]).flatMap Atom.vars)
              ((Bindings.merge partBnd p'.2).head?.getD p'.2)) p'.1).2)
    (hroot :
      ∀ acc : List (Atom × Bindings) × St,
        P acc.2 →
          (root, rootBnd) ∈
            (interpretFuel env (fuel + 1) acc.2
              [evalItemNil (Atom.expr [Atom.sym op, p, atom', templ])] []).1)
    (hRootBndEmpty :
      restrictBnd (([p, atom, templ]).flatMap Atom.vars)
        ((Bindings.merge [] rootBnd).head?.getD rootBnd) = [])
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, p, atom', templ]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal :
      ∀ st0,
        P st0 →
          (final, []) ∈
            (mettaEval env fuel st0
              (restrictBnd (([p, atom, templ]).flatMap Atom.vars)
                ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, p, atom, templ])).1 := by
  let qvars := p.vars ++ (atom.vars ++ templ.vars)
  let parts0 : List (List Atom × Bindings) :=
    argPairs.map (fun q : Atom × Bindings =>
      ([p, q.1], restrictBnd qvars ((Bindings.merge [] q.2).head?.getD q.2)))
  let appendTempl :=
    fun acc2 : List (List Atom × Bindings) × St => fun part0 : List Atom × Bindings =>
      (acc2.1 ++ [(part0.1 ++ [instantiate part0.2 templ], part0.2)], acc2.2)
  let parts : List (List Atom × Bindings) :=
    parts0.map (fun part0 => (part0.1 ++ [instantiate part0.2 templ], part0.2))
  let part : List Atom × Bindings := ([p, atom', templ], [])
  have hArg1 : (mettaEval env fuel st [] atom).1 = argPairs := by
    simp [hArg]
  have hArg2 : (mettaEval env fuel st [] atom).2 = stArg := by
    simp [hArg]
  have hpart : part ∈ parts := by
    refine List.mem_map.mpr ?_
    refine ⟨([p, atom'], []), ?_, by simp [part, Metta.instantiate_nil]⟩
    refine List.mem_map.mpr ?_
    exact ⟨(atom', []), hmemArg, by simp [qvars, restrictBnd_empty_merge_empty]⟩
  have hNoErrPart :
      (part.1.zip [p, atom, templ]).find? (fun ho => ho.1.isError && ho.1 != ho.2) = none := by
    simpa [part] using hNoErr
  have hrecState' :
      ∀ (partBnd : Bindings)
        (acc : List (Atom × Bindings) × St) (p' : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd qvars ((Bindings.merge partBnd p'.2).head?.getD p'.2)) p'.1).2 := by
    intro partBnd acc p' hP
    simpa [qvars] using hrecState partBnd acc p' hP
  have hFinal' :
      ∀ st0,
        P st0 →
          (final, []) ∈
            (mettaEval env fuel st0
              (restrictBnd qvars ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1 := by
    intro st0 hP
    simpa [qvars] using hFinal st0 hP
  have hRootBndEmpty' :
      restrictBnd qvars ((Bindings.merge [] rootBnd).head?.getD rootBnd) = [] := by
    simpa [qvars] using hRootBndEmpty
  have hprep :
      List.foldl appendTempl ([], stArg) parts0 = (parts, stArg) := by
    have hprepGen :
        ∀ (pref : List (List Atom × Bindings)) (ps : List (List Atom × Bindings)),
          List.foldl appendTempl (pref, stArg) ps =
            (pref ++ ps.map (fun part0 => (part0.1 ++ [instantiate part0.2 templ], part0.2)), stArg) := by
      intro pref ps
      induction ps generalizing pref with
      | nil =>
          simp [appendTempl]
      | cons x xs ih =>
          simp [appendTempl, ih, List.append_assoc]
    simpa [parts] using hprepGen [] parts0
  have hprep1 :
      (List.foldl appendTempl ([], stArg) parts0).1 = parts := by
    simp [hprep]
  have hprep2 :
      (List.foldl appendTempl ([], stArg) parts0).2 = stArg := by
    simp [hprep]
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, p, atom, templ])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  rw [hArg1, hArg2]
  rw [hprep1, hprep2]
  have hstepEq :
      mettaEvalExprPartFoldStep env fuel qvars op [p, atom, templ] [] (returnsAtom selected) =
        (fun acc part =>
          match List.find? (fun ho => ho.1.isError && ho.1 != ho.2) (part.1.zip [p, atom, templ]) with
          | some (err, _) => (acc.1 ++ [(err, part.2)], acc.2)
          | none =>
              (acc.1 ++
              (List.foldl
                  (fun a2 p_1 =>
                        if (p_1.1 == notReducibleA) = true ∨
                            (p_1.1 == Atom.expr (Atom.sym op :: part.1)) = true then
                          (a2.1 ++ [(Atom.expr (Atom.sym op :: part.1), part.2)], a2.2)
                        else
                          if returnsAtom selected = true then
                            (a2.1 ++
                                [(p_1.1,
                                    restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                      ((part.2.merge p_1.2).head?.getD p_1.2))],
                              a2.2)
                          else
                            (a2.1 ++
                                List.map
                                  (fun m =>
                                    (m.1,
                                      restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                        (((restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                              ((part.2.merge p_1.2).head?.getD p_1.2)).merge
                                            m.2).head?.getD m.2)))
                                  (mettaEval env fuel a2.2
                                      (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                        ((part.2.merge p_1.2).head?.getD p_1.2))
                                      p_1.1).1,
                              (mettaEval env fuel a2.2
                                  (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                    ((part.2.merge p_1.2).head?.getD p_1.2))
                                  p_1.1).2))
                      ([],
                        (interpretFuel env (fuel + 1) acc.2
                            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                                Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).2)
                      (interpretFuel env (fuel + 1) acc.2
                          [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                              Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).1).1,
                (List.foldl
                    (fun a2 p_1 =>
                      if (p_1.1 == notReducibleA) = true ∨
                          (p_1.1 == Atom.expr (Atom.sym op :: part.1)) = true then
                        (a2.1 ++ [(Atom.expr (Atom.sym op :: part.1), part.2)], a2.2)
                      else
                        if returnsAtom selected = true then
                          (a2.1 ++
                              [(p_1.1,
                                  restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                    ((part.2.merge p_1.2).head?.getD p_1.2))],
                            a2.2)
                        else
                          (a2.1 ++
                              List.map
                                (fun m =>
                                  (m.1,
                                    restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                      (((restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                            ((part.2.merge p_1.2).head?.getD p_1.2)).merge
                                          m.2).head?.getD m.2)))
                                (mettaEval env fuel a2.2
                                    (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                      ((part.2.merge p_1.2).head?.getD p_1.2))
                                    p_1.1).1,
                            (mettaEval env fuel a2.2
                                (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                  ((part.2.merge p_1.2).head?.getD p_1.2))
                                p_1.1).2))
                    ([],
                      (interpretFuel env (fuel + 1) acc.2
                          [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                              Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).2)
                    (interpretFuel env (fuel + 1) acc.2
                        [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                            Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).1).2)) := by
    funext acc part
    unfold mettaEvalExprPartFoldStep
    split
    · rfl
    · have hrootEq :
          (fun a2 p_1 =>
            if (p_1.1 == notReducibleA) = true ∨
                (p_1.1 == Atom.expr (Atom.sym op :: part.1)) = true then
              (a2.1 ++ [(Atom.expr (Atom.sym op :: part.1), part.2)], a2.2)
            else
              if returnsAtom selected = true then
                (a2.1 ++
                    [(p_1.1,
                        restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                          ((part.2.merge p_1.2).head?.getD p_1.2))],
                  a2.2)
              else
                (a2.1 ++
                    List.map
                      (fun m =>
                        (m.1,
                          restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                            (((restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                                        ((part.2.merge p_1.2).head?.getD p_1.2)).merge
                                    m.2).head?.getD
                              m.2)))
                      (mettaEval env fuel a2.2
                          (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                            ((part.2.merge p_1.2).head?.getD p_1.2))
                          p_1.1).1,
                  (mettaEval env fuel a2.2
                      (restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
                        ((part.2.merge p_1.2).head?.getD p_1.2))
                      p_1.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars (Atom.expr (Atom.sym op :: part.1)) part.2
            (returnsAtom selected) := by
        funext a2 p_1
        simp [mettaEvalExprRootFoldStep, qvars]
      simp [hrootEq]
  have hfold :=
    mettaEvalExprPartFold_evals_selected_readout_state_pred
      env fuel qvars op [p, atom, templ] [] (returnsAtom selected) P parts ([], stArg)
      part (root, rootBnd) final
      hinit hpart hNoErrPart hrootState hrecState'
      (by
        intro acc hP
        simpa [part, evalItemNil] using hroot acc hP)
      hRootNotNotReducible hRootNotSelf hReturns
      (by
        intro st0 hP
        simpa [part] using hFinal' st0 hP)
  have hfold' :
      (final, []) ∈
        (parts.foldl
          (mettaEvalExprPartFoldStep env fuel qvars op [p, atom, templ] [] (returnsAtom selected))
          ([], stArg)).1 := by
    simpa [part, qvars, hRootBndEmpty', restrictBnd_empty_merge_empty] using hfold
  change
    (final, []) ∈
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel qvars op [p, atom, templ] [] (returnsAtom selected))
        ([], stArg)).1
  exact hfold'

/-- Membership-shaped ternary expression fold for an evaluated/quoted/quoted argument mask.

This is the executable scheduler shape of stdlib `if`: evaluate the Boolean
condition, quote both branches, reduce the rebuilt root expression, then
recursively evaluate the selected branch.  As with the other scheduler folds,
the theorem is generic in the operator and environment; callers provide the
operator's concrete signature facts. -/
theorem mettaEval_ternary_expr_mem_of_eval_quoted_quoted_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st stCond : St)
    (op : String)
    (cond thenA elseA cond' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hCond : mettaEval env fuel st [] cond = ([(cond', [])], stCond))
    (hSelected : selectFunctionType env st.world (.sym op) [cond, thenA, elseA] = .selected selected)
    (hMask : argMask selected 3 = [true, false, false])
    (hNoErr :
      (([cond', thenA, elseA].zip [cond, thenA, elseA]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) stCond
        [evalItemNil (Atom.expr [Atom.sym op, cond', thenA, elseA])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, cond', thenA, elseA]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0,
      (final, []) ∈
        (mettaEval env fuel st0
          (restrictBnd (([cond, thenA, elseA]).flatMap Atom.vars)
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1) :
    (final,
        restrictBnd (([cond, thenA, elseA]).flatMap Atom.vars)
          (((restrictBnd (([cond, thenA, elseA]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, cond, thenA, elseA])).1 := by
  let qvars := ([cond, thenA, elseA]).flatMap Atom.vars
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, cond, thenA, elseA])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hCond]
  simp [restrictBnd_empty_merge_empty]
  rw [Metta.instantiate_nil thenA]
  rw [Metta.instantiate_nil elseA]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => ho.1.isError && ho.1 != ho.2)
        [(cond', cond), (thenA, thenA), (elseA, elseA)] = none := by
    simpa using hNoErr
  rw [hNoErr']
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, cond', thenA, elseA]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) stCond [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, cond', thenA, elseA])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel qvars (Atom.expr [Atom.sym op, cond', thenA, elseA]) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [qvars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, cond', thenA, elseA]) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, cond', thenA, elseA], [])], a2.2)
          else if returnsAtom selected = true then
            (a2.1 ++
              [(p.1,
                restrictBnd (cond.vars ++ (thenA.vars ++ elseA.vars))
                  ((Bindings.merge [] p.2).head?.getD p.2))],
              a2.2)
          else
            (a2.1 ++
                (mettaEval env fuel a2.2
                  (restrictBnd (cond.vars ++ (thenA.vars ++ elseA.vars))
                    ((Bindings.merge [] p.2).head?.getD p.2)) p.1).1.map (fun m =>
                    (m.1,
                      restrictBnd (cond.vars ++ (thenA.vars ++ elseA.vars))
                        ((Bindings.merge
                          (restrictBnd (cond.vars ++ (thenA.vars ++ elseA.vars))
                            ((Bindings.merge [] p.2).head?.getD p.2)) m.2).head?.getD m.2))),
              (mettaEval env fuel a2.2
                (restrictBnd (cond.vars ++ (thenA.vars ++ elseA.vars))
                  ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)) =
          mettaEvalExprRootFoldStep env fuel qvars
            (Atom.expr [Atom.sym op, cond', thenA, elseA]) [] (returnsAtom selected) by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, qvars]]
      simpa [qvars] using hfold

/-- Membership-shaped closed four-argument expression fold for executable `mettaEval`.

This is the arity-four sibling of
`mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem`.  It is the scheduler lift needed
for embedded `(unify atom pattern then else)`: the four arguments are evaluated left-to-right, the
rebuilt root is interpreted once, and the selected root readout is recursively evaluated.  The
theorem stays generic in the operator and root readout; it does not unfold a concrete `unify`
trace. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hwClosed : w.vars = []) (hxClosed : x.vars = [])
    (hyClosed : y.vars = []) (hzClosed : z.vars = [])
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, w, x, y, z])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hw]
  simp [hwClosed, hxClosed, hyClosed, hzClosed, restrictBnd_nil_vars]
  rw [hx]
  simp
  rw [hy]
  simp
  rw [hz]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  simp only [List.nil_append]
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval",
        Atom.expr [Atom.sym op, w', x', y', z']]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st₄ [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem :
            [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel [] (Atom.expr [Atom.sym op, w', x', y', z']) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [restrictBnd_nil_vars] using hFinal st0)
      rw [show
        (fun a2 p =>
          if (p.1 == notReducibleA) = true ∨
              (p.1 == Atom.expr [Atom.sym op, w', x', y', z']) = true then
            (a2.1 ++ [(Atom.expr [Atom.sym op, w', x', y', z'], [])], a2.2)
          else if returnsAtom selected = true then
            (a2.1 ++ [(p.1, [])], a2.2)
          else
            (a2.1 ++ (mettaEval env fuel a2.2 [] p.1).1.map (fun m => (m.1, [])),
              (mettaEval env fuel a2.2 [] p.1).2)) =
          mettaEvalExprRootFoldStep env fuel []
            (Atom.expr [Atom.sym op, w', x', y', z']) [] (returnsAtom selected) by
        funext a2 p
        simp [mettaEvalExprRootFoldStep, restrictBnd_nil_vars]]
      simpa [restrictBnd_nil_vars] using hfold

/-- Exact-state closed four-argument expression fold for executable `mettaEval`.

This is the state-specific sibling of
`mettaEval_quaternary_expr_mem_of_arg_singletons_and_root_eval_member`.  It is useful when the
selected root readout is known exactly, so the recursive evaluation premise only has to hold at the
actual threaded root state rather than for every possible `World`. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_root_eval_eq
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ stRoot : St)
    (op : String)
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hwClosed : w.vars = []) (hxClosed : x.vars = [])
    (hyClosed : y.vars = []) (hzClosed : z.vars = [])
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, w, x, y, z])]
  simp only
  rw [hSelected]
  simp only [evaluateSelectedApplication, hMask, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hw]
  simp [hwClosed, hxClosed, hyClosed, hzClosed, restrictBnd_nil_vars]
  rw [hx]
  simp
  rw [hy]
  simp
  rw [hz]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hNoErr]
  simp only [List.nil_append]
  have hRoot' :
      interpretFuel env (fuel + 1) st₄
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, w', x', y', z']]) [] }] [] =
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
    (op : String) (arg out : Atom) (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [true])
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
      env fuel st stArg stRoot op arg out selected hArg hSelected hMask hNotError hroot
  exact
    mettaEval_singleton_readout_sound env (fuel + 1) st []
      (Atom.expr [Atom.sym op, arg]) (Atom.expr [Atom.sym op, out])
      (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) stRoot R hEval hReach

/-! ## Atom-typed unary expression fold -/

/-- Membership-shaped unary fold for Atom-typed arguments whose root readout is evaluated.

When the selected signature has `argMask selected 1 = [false]`, the executable `mettaEval` loop keeps the argument as an
Atom, evaluates the rebuilt root `(op arg)`, and, if that root is neither `NotReducible` nor an
Atom-valued final result, recursively evaluates the root readout. This is the unary analogue of
`mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem` for operators such as `is-bad`. -/
theorem mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st stRoot : St)
    (op : String) (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [false])
    (hRoot : interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, arg]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp only
  rw [hSelected]
  simp [evaluateSelectedApplication, hMask, hArgClosed, hArgNoErr, hArgSelf, instantiate_nil]
  have hRoot' :
      interpretFuel env (fuel + 1) st
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, arg]]) [], bnd := [] }] [] =
      ([(root, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  simp [hRootNotNotReducible, hRootNotSelf, hReturns, restrictBnd_nil_vars]
  exact ⟨[], by simpa [restrictBnd_nil_vars] using hFinal⟩

/-- Membership-shaped unary fold for Atom-typed arguments and selected root readouts.

This is the root-membership companion to
`mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_mem`: it is the right shape when the
root equality-rule bridge supplies the runtime-freshened readout as a member rather than proving
the whole root-readout list is a singleton. -/
theorem mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [false])
    (hRoot : (root, rootBnd) ∈ (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, arg]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp only
  rw [hSelected]
  simp [evaluateSelectedApplication, hMask, hArgClosed, hArgNoErr, hArgSelf, instantiate_nil]
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, arg]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem : [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, arg])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states
          env fuel [] (Atom.expr [Atom.sym op, arg]) [] (returnsAtom selected)
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns (by
            intro st0
            simpa [restrictBnd_nil_vars] using hFinal st0)
      change (final, []) ∈
        (List.foldl
          (mettaEvalExprRootFoldStep env fuel [] (Atom.expr [Atom.sym op, arg]) []
            (returnsAtom selected))
          ([], stRoot) pairs).1
      simpa [restrictBnd_nil_vars] using hfold

/-- State-invariant version of
`mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_member`.

The recursive root readout may only be sound under a state invariant.  This theorem carries that
invariant from the root `interpretFuel` result through the selected-readout fold. -/
theorem mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_member_state_pred
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hMask : argMask selected 1 = [false])
    (hRoot : (root, rootBnd) ∈ (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] []).1)
    (hRootState : P (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] []).2)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, arg]) = false)
    (hReturns : returnsAtom selected = false)
    (hstep :
      ∀ (acc : List (Atom × Bindings) × St) (p : Atom × Bindings),
        P acc.2 →
          P (mettaEval env fuel acc.2
            (restrictBnd ([] : List String) ((Bindings.merge [] p.2).head?.getD p.2)) p.1).2)
    (hFinal : ∀ st0,
      P st0 → (final, []) ∈ (mettaEval env fuel st0 [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  unfold mettaEval
  rw [instantiate_nil (Atom.expr [Atom.sym op, arg])]
  simp only
  rw [hSelected]
  simp [evaluateSelectedApplication, hMask, hArgClosed, hArgNoErr, hArgSelf, instantiate_nil]
  let rootItem : Item :=
    { stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, arg]]) [],
      bnd := [] }
  cases hpairs : interpretFuel env (fuel + 1) st [rootItem] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        have hrootItem : [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, arg])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRoot
        exact hRoot
      have hRootState' : P stRoot := by
        have hrootItem : [rootItem] = [evalItemNil (Atom.expr [Atom.sym op, arg])] := by
          simp [rootItem, evalItemNil]
        rw [hrootItem] at hpairs
        rw [hpairs] at hRootState
        exact hRootState
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_state_pred
          env fuel [] (Atom.expr [Atom.sym op, arg]) [] (returnsAtom selected) P
          (root, rootBnd) pairs stRoot final
          hRootPairs hRootNotNotReducible hRootNotSelf hReturns hRootState'
          hstep
          (by
            intro st0 hP
            simpa [restrictBnd_nil_vars] using hFinal st0 hP)
      change (final, []) ∈
        (List.foldl
          (mettaEvalExprRootFoldStep env fuel [] (Atom.expr [Atom.sym op, arg]) []
            (returnsAtom selected))
          ([], stRoot) pairs).1
      simpa [restrictBnd_nil_vars] using hfold

/-- Soundness package for a closed binary expression whose evaluator result is obtained by the
generic binary fold.

The relation proof is split in the same way as the evaluator: a root relation chain from the
original application to the root readout, followed by a recursive relation chain from that root
readout to the final readout. -/
theorem mettaEval_binary_expr_singleton_sound_of_arg_singletons_and_root_eval
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : mettaEval env fuel stRoot [] root = ([(final, [])], stOut))
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinalReach : Relation.ReflTransGen R root final) :
    ∀ out bnd,
      (out, bnd) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 →
        bnd = [] ∧ Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) out := by
  have hEval :=
    mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval
      env fuel st st₁ st₂ stRoot stOut op x y x' y' root final rootBnd
      selected hxClosed hyClosed hx hy hSelected hMask hNoErr hRoot hRootNotNotReducible
      hRootNotSelf hReturns hFinal
  exact
    mettaEval_singleton_readout_sound env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])
      final [] stOut R hEval (hRootReach.trans hFinalReach)

/-- Specific-member soundness package for a closed binary expression.

This is the induction-friendly counterpart of
`mettaEval_binary_expr_singleton_sound_of_arg_singletons_and_root_eval`.  The recursive evaluation of
the root readout is represented by one actual membership proof and the relation chain for that same
readout, not by singleton equality or Peano-specific fuel arithmetic. -/
theorem mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hPolicy : ExactApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnAtom = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalReach : Relation.ReflTransGen R root final) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final := by
  constructor
  · exact
      mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem_of_exactPolicy
        env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
        mask returnAtom hxClosed hyClosed hx hy hPolicy hMask hNoErr hRoot hRootNotNotReducible hRootNotSelf
        hReturns hFinal
  · exact hRootReach.trans hFinalReach

/-- Selected-signature specialization of the binary member relation package. -/
theorem mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalReach : Relation.ReflTransGen R root final) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final := by
  exact mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
    (argMask selected 2) (returnsAtom selected) R hxClosed hyClosed hx hy
    (.selected selected hSelected) hMask hNoErr hRoot hRootNotNotReducible hRootNotSelf
    hReturns hRootReach hFinal hFinalReach

/-- IH-shaped soundness package for a closed binary expression.

This version is convenient when an induction hypothesis provides soundness for every recursive
readout of the root result. It is a thin wrapper around the specific-member theorem above. -/
theorem mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinalSound :
      ∀ final, (final, []) ∈ (mettaEval env fuel stRoot [] root).1 →
        Relation.ReflTransGen R root final)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final :=
  mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd selected R
    hxClosed hyClosed hx hy hSelected hMask hNoErr hRoot hRootNotNotReducible hRootNotSelf
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
