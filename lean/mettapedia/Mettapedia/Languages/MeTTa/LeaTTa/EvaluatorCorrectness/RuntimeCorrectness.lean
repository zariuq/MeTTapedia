import MettaHyperonFull.Proofs.Results
import MettaHyperonFull.Proofs.TypeSoundness
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

/-! ## Published success-priority algebra -/

/-- Applying the published success-priority boundary to a singleton changes
neither the result nor the threaded state. -/
@[simp] theorem prioritizeSemanticResults_singleton
    (result : Atom × Bindings) (st : St) :
    prioritizeSemanticResults ([result], st) = ([result], st) := by
  cases hError : result.1.isError <;>
    simp [prioritizeSemanticResults, hError]

/-- Success priority filters only the result list; the state reached while
discovering those results is preserved exactly. -/
@[simp] theorem prioritizeSemanticResults_snd
    (execution : List (Atom × Bindings) × St) :
    (prioritizeSemanticResults execution).2 = execution.2 := by
  unfold prioritizeSemanticResults
  change
    (if (execution.1.filter (fun result => !result.1.isError)).isEmpty = true then
        execution
      else
        (execution.1.filter (fun result => !result.1.isError), execution.2)).2 =
      execution.2
  by_cases hEmpty :
      (execution.1.filter (fun result => !result.1.isError)).isEmpty = true
  · rw [if_pos hEmpty]
  · rw [if_neg hEmpty]

/-- A non-error readout survives the published success-priority boundary.
Errors intentionally have no corresponding unconditional theorem: they are
suppressed whenever the same execution contains a success. -/
theorem mem_prioritizeSemanticResults_of_mem_of_not_error
    {execution : List (Atom × Bindings) × St} {result : Atom × Bindings}
    (hmem : result ∈ execution.1) (hError : result.1.isError = false) :
    result ∈ (prioritizeSemanticResults execution).1 := by
  unfold prioritizeSemanticResults
  by_cases hEmpty :
      (execution.1.filter (fun candidate => !candidate.1.isError)).isEmpty = true
  · simp [hEmpty, hmem]
  · simp [hEmpty, List.mem_filter, hmem, hError]

/-- Every readout retained by the published success-priority boundary came
from the underlying execution.  This direction needs no error-side premise:
priority only filters the discovered list and never manufactures a result. -/
theorem mem_of_mem_prioritizeSemanticResults
    {execution : List (Atom × Bindings) × St} {result : Atom × Bindings}
    (hmem : result ∈ (prioritizeSemanticResults execution).1) :
    result ∈ execution.1 := by
  unfold prioritizeSemanticResults at hmem
  by_cases hEmpty :
      (execution.1.filter (fun candidate => !candidate.1.isError)).isEmpty = true
  · simpa [hEmpty] using hmem
  · have hFiltered :
        result ∈ execution.1.filter (fun candidate => !candidate.1.isError) := by
      simpa [hEmpty] using hmem
    exact (List.mem_filter.mp hFiltered).1

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
nor a headless LHS, they do not change the executable candidate set in the
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
it before a core rule set leaves the core candidate set unchanged. -/
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

This is the B2 induction principle: later soundness proofs should rewrite by this lemma and apply the
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
  have rawEmpty : restrictBndRaw [] b = [] := by
    unfold restrictBndRaw
    change b.filter
      (fun r => match r with | BindingRel.eq _ _ => false | _ => false) = []
    apply List.filter_eq_nil_iff.mpr
    intro relation _member
    cases relation <;> simp
  simp [restrictBnd, rawEmpty, Bindings.merge]

/-- Bare variables compare equal to themselves under LeaTTa's structural `BEq`.

This is intentionally only the variable fragment; `BEq Atom` is not globally lawful because
grounded floats inherit host IEEE equality. -/
theorem atom_var_beq_self_true (v : VarName) :
    (Atom.var v == Atom.var v) = true := by
  change Atom.beq (Atom.var v) (Atom.var v) = true
  simp [Atom.beq]

/-- Repeating one public variable in a retention scope does not duplicate its
canonical value binding.  The hypotheses expose exactly the three runtime
facts needed at this boundary: resolution reaches the value, the value is not
a variable alias, and reconciling the repeated value is inert. -/
theorem restrictBnd_triple_singleton_val
    (binder : VarName) (value : Atom)
    (hresolve :
      resolveAtom [BindingRel.val binder value] 2 (Atom.var binder) = value)
    (hnotvar : ∀ name, value ≠ Atom.var name)
    (hunify : Bindings.unifyValues [value, value] = some []) :
    restrictBnd [binder, binder, binder]
        [BindingRel.val binder value] =
      [BindingRel.val binder value] := by
  let relation := BindingRel.val binder value
  have hresolve' : resolveAtom [relation] 2 (Atom.var binder) = value := by
    simpa [relation] using hresolve
  have hraw :
      restrictBndRaw [binder, binder, binder] [relation] =
        [relation, relation, relation] := by
    unfold restrictBndRaw
    simp only [List.filterMap_cons, List.filterMap_nil, List.length_cons,
      List.length_nil, Nat.reduceAdd]
    rw [hresolve']
    cases value <;> simp_all [relation]
  have hsame :
      Bindings.addVarBinding [relation] binder value = [[relation]] := by
    apply Bindings.addVarBinding_nochange (values := [value])
    · exact hnotvar
    · change Bindings.classValues [BindingRel.val binder value] binder = [value]
      exact Bindings.classValues_singleton_val_self binder value
    · simp
    · simpa using hunify
  have hfirst : Bindings.mergeOne [[]] relation = [[relation]] := by
    unfold Bindings.mergeOne
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change Bindings.addVarBinding [] binder value = [[relation]]
    rw [Bindings.addVarBinding_fresh (by simp) hnotvar]
    simp [Bindings.addValRaw, Bindings.removeVal, relation]
  have hsameStep :
      Bindings.mergeOne [[relation]] relation = [[relation]] := by
    simpa [Bindings.mergeOne, relation] using hsame
  have hmergeRepeated :
      Bindings.merge [] [relation, relation, relation] = [[relation]] := by
    change Bindings.mergeOne
        (Bindings.mergeOne (Bindings.mergeOne [[]] relation) relation)
        relation = [[relation]]
    rw [hfirst, hsameStep, hsameStep]
  change restrictBnd [binder, binder, binder] [relation] = [relation]
  unfold restrictBnd
  rw [hraw]
  dsimp only
  rw [hmergeRepeated]
  rfl

/-- A fresh `let` binder that still resolves to itself contributes no retained
binding, even when the public scope contains the binder three times.  The two
value bindings are private siblings; the sole equality has a fresh left
endpoint, so it is filtered from the public projection. -/
theorem restrictBnd_triple_fresh_let_binder
    (binder templateKey atomKey patternKey : VarName)
    (template atom : Atom)
    (hPatternFresh : patternKey ≠ binder)
    (hresolve :
      resolveAtom
          [ BindingRel.val templateKey template
          , BindingRel.val atomKey atom
          , BindingRel.eq patternKey binder ]
          4 (Atom.var binder) = Atom.var binder) :
    restrictBnd [binder, binder, binder]
        [ BindingRel.val templateKey template
        , BindingRel.val atomKey atom
        , BindingRel.eq patternKey binder ] = [] := by
  have hraw :
      restrictBndRaw [binder, binder, binder]
          [ BindingRel.val templateKey template
          , BindingRel.val atomKey atom
          , BindingRel.eq patternKey binder ] = [] := by
    have hlen :
        [ BindingRel.val templateKey template
        , BindingRel.val atomKey atom
        , BindingRel.eq patternKey binder ].length + 1 = 4 := by
      rfl
    unfold restrictBndRaw
    simp only [List.filterMap_cons, List.filterMap_nil]
    rw [hlen, hresolve]
    simp [hPatternFresh]
  unfold restrictBnd
  rw [hraw]
  rfl

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
  have rawEmpty : restrictBndRaw vars ([] : Bindings) = [] := by
    simp [restrictBndRaw, resolveAtom_nil_var]
  simp [restrictBnd, rawEmpty, Bindings.merge]

/-- An empty raw public projection remains empty after canonical replay.

This is the stable boundary for proofs that separately establish the solved
and retained-equality components of `restrictBndRaw` are empty. -/
theorem restrictBnd_eq_nil_of_raw_eq_nil
    (vars : List VarName) (bindings : Bindings)
    (hraw : restrictBndRaw vars bindings = []) :
    restrictBnd vars bindings = [] := by
  unfold restrictBnd
  rw [hraw]
  rfl

/-- A public scope whose variables all remain unresolved contributes no
binding when the input contains no equality wholly internal to that scope.

The two premises correspond exactly to the solved-binding and retained-equality
components of `restrictBndRaw`; in particular, this theorem does not discard a
public equality edge. -/
theorem restrictBnd_eq_nil_of_resolves_self_and_no_public_eqs
    (vars : List VarName) (bindings : Bindings)
    (hresolve : ∀ name ∈ vars,
      resolveAtom bindings (bindings.length + 1) (Atom.var name) = Atom.var name)
    (heqs :
      bindings.filter (fun relation =>
        match relation with
        | BindingRel.eq left right =>
            vars.contains left && vars.contains right
        | _ => false) = []) :
    restrictBnd vars bindings = [] := by
  have hsolved :
      vars.filterMap (fun name =>
        let value := resolveAtom bindings (bindings.length + 1) (Atom.var name)
        match value with
        | Atom.var target =>
            if target == name then none else some (BindingRel.eq name target)
        | _ => some (BindingRel.val name value)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro name hname
    rw [hresolve name hname]
    simp
  apply restrictBnd_eq_nil_of_raw_eq_nil
  unfold restrictBndRaw
  change
    (vars.filterMap (fun name =>
        let value := resolveAtom bindings (bindings.length + 1) (Atom.var name)
        match value with
        | Atom.var target =>
            if target == name then none else some (BindingRel.eq name target)
        | _ => some (BindingRel.val name value)) ++
      bindings.filter (fun relation =>
        match relation with
        | BindingRel.eq left right =>
            vars.contains left && vars.contains right
        | _ => false)) = []
  rw [hsolved, heqs]
  rfl

/-- Empty argument readouts remain empty after LeaTTa's merge-and-retain step, even when the
surrounding expression has query variables. -/
theorem restrictBnd_empty_merge_empty (vars : List VarName) :
    restrictBnd vars ((Bindings.merge [] ([] : Bindings)).head?.getD []) = [] := by
  simp [Bindings.merge, restrictBnd_nil_bindings]

/-- An empty selected theory contributes exactly the incoming application
binding.  This is the raw-theory form used after the operator-head cast; it is
separate from the selected-policy projection because the cast theory need not
equal the applicability theory for polymorphic operators. -/
@[simp] theorem selectedApplicationInitialBindingsFromTheory_nil
    (incoming : Bindings) (expression expected : Atom) :
    selectedApplicationInitialBindingsFromTheory incoming expression expected [] =
      [incoming] := by
  simp [selectedApplicationInitialBindingsFromTheory,
    restrictBnd_nil_bindings, Bindings.merge]

/-- The selected-policy wrapper is exactly the raw-theory merge against its
caller-visible projection.  Downstream proofs should consume this equation
rather than depend on the wrapper's current definitional factoring. -/
@[simp] theorem selectedApplicationInitialBindings_eq_merge_visible
    (incoming : Bindings) (expression expected : Atom)
    (selected : SelectedFunctionType) :
    selectedApplicationInitialBindings incoming expression expected selected =
      Bindings.merge incoming
        (selectedApplicationVisibleBindings expression expected selected) := by
  rfl

/-- A selected policy with no type bindings contributes exactly the incoming
application binding.  This is the compatibility boundary used by concrete
monomorphic operator policies after repair #19 made nonempty public type
bindings observable. -/
theorem selectedApplicationInitialBindings_of_typeBindings_nil
    (incoming : Bindings) (expression expected : Atom)
  (selected : SelectedFunctionType) (hTypeBindings : selected.typeBindings = []) :
    selectedApplicationInitialBindings incoming expression expected selected =
      [incoming] := by
  simp [selectedApplicationInitialBindings,
    hTypeBindings]

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

This is the reusable fuel-indexed theorem for open matcher values: the binding set need not be closed,
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

This is the compact Gate-2 theorem package for static symbol-headed rules with
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

/-- Exact companion of `mem_interpretFuel_single_of_mem_interpretStack1_final`:
one scheduler step producing exactly one nonempty final item is harvested as
exactly one `(atom, bindings)` pair with the scheduler's output state. -/
theorem interpretFuel_single_of_interpretStack1_single_final
    (env : MinEnv) (fuel : Nat) (st st' : St) (it out : Item)
    (hstep : interpretStack1 env fuel st it = ([out], st'))
    (hfinal : isFinal out = true)
    (hnotEmpty : ((finalPair out).1 != emptyA) = true) :
    interpretFuel env (fuel + 1) st [it] [] = ([finalPair out], st') := by
  simp [interpretFuel, hstep, hfinal, hnotEmpty]

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
  have _ := hreadout
  by_cases hEmpty : (Atom.sym op == emptyA) = true
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]

/-- Exact version of `mettaEval_symbol_keeps_of_notReducible_readout` for the common structural
case where the root fuel driver returns exactly the singleton `NotReducible` readout and preserves
state. -/
theorem mettaEval_symbol_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (op : String)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.sym op]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.sym op) = ([(Atom.sym op, bnd)], st) := by
  have _ := hreadout
  by_cases hEmpty : (Atom.sym op == emptyA) = true
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]

/-- Full `mettaEval` keeps a bare grounded atom when the root minimal interpreter reports
`NotReducible`. This is the Boolean-control-flow sibling of
`mettaEval_symbol_keeps_of_notReducible_readout`. -/
theorem mettaEval_ground_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (g : Ground)
    (hreadout : (notReducibleA, bnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.gnd g]) [], bnd := bnd }] []).1) :
    (Atom.gnd g, bnd) ∈ (mettaEval env (fuel + 1) st bnd (Atom.gnd g)).1 := by
  have _ := hreadout
  by_cases hEmpty : (Atom.gnd g == emptyA) = true
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]
  · by_cases hError : (Atom.gnd g).isError = true
    · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty, hError]
    · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty, hError]

/-- Exact version of `mettaEval_ground_keeps_of_notReducible_readout`. -/
theorem mettaEval_ground_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (g : Ground)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.gnd g]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.gnd g) = ([(Atom.gnd g, bnd)], st) := by
  have _ := hreadout
  by_cases hEmpty : (Atom.gnd g == emptyA) = true
  · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty]
  · by_cases hError : (Atom.gnd g).isError = true
    · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty, hError]
    · simp [mettaEval, Metta.instantiate, Metta.Bindings.resolveAtom, hEmpty, hError]

/-- Full `mettaEval` keeps a bare variable when the root minimal interpreter reports
`NotReducible`. -/
theorem mettaEval_var_keeps_of_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (v : VarName)
    (hinst : instantiate bnd (Atom.var v) = Atom.var v)
    (hreadout : (notReducibleA, bnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.var v]) [], bnd := bnd }] []).1) :
    (Atom.var v, bnd) ∈ (mettaEval env (fuel + 1) st bnd (Atom.var v)).1 := by
  have _ := hreadout
  by_cases hEmpty : (Atom.var v == emptyA) = true
  · simp [mettaEval, hinst, hEmpty]
  · simp [mettaEval, hinst, hEmpty]

/-- Exact version of `mettaEval_var_keeps_of_notReducible_readout`. -/
theorem mettaEval_var_eq_of_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (v : VarName)
    (hinst : instantiate bnd (Atom.var v) = Atom.var v)
    (hreadout : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.var v]) [], bnd := bnd }] [] =
      ([(notReducibleA, bnd)], st)) :
    mettaEval env (fuel + 1) st bnd (Atom.var v) = ([(Atom.var v, bnd)], st) := by
  have _ := hreadout
  by_cases hEmpty : (Atom.var v == emptyA) = true
  · simp [mettaEval, hinst, hEmpty]
  · simp [mettaEval, hinst, hEmpty]

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

/-- Binding-general form of
`mettaEval_expr_root_evals_selected_readout_all_states`.

The recursive evaluator may retain public bindings.  The outer fold merges
those bindings with the public projection already obtained from the selected
root readout; no empty-binding coincidence is assumed. -/
theorem mettaEval_expr_root_evals_selected_readout_all_states_bnd
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (w : Atom) (partBnd : Bindings) (returnAtom : Bool)
    (p : Atom × Bindings) (pairs : List (Atom × Bindings)) (st : St)
    (final : Atom) (finalBnd : Bindings)
    (hmem : p ∈ pairs)
    (hnotNR : (p.1 == notReducibleA) = false)
    (hnotSelf : (p.1 == w) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0,
      (final, finalBnd) ∈
        (mettaEval env fuel st0
          (restrictBnd queryVars
            ((Bindings.merge partBnd p.2).head?.getD p.2)) p.1).1) :
    (final,
        restrictBnd queryVars
          (((restrictBnd queryVars
              ((Bindings.merge partBnd p.2).head?.getD p.2)).merge
              finalBnd).head?.getD finalBnd)) ∈
      (pairs.foldl
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom)
        ([], st)).1 := by
  rcases List.mem_iff_append.mp hmem with ⟨pre, post, hpairs⟩
  rw [hpairs, List.foldl_append]
  simp only [List.foldl_cons]
  let accPre :=
    pre.foldl
      (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom)
      ([], st)
  have hfirst :
      ¬ ((p.1 == notReducibleA) = true ∨ (p.1 == w) = true) := by
    intro h
    rcases h with hnr | hself
    · rw [hnotNR] at hnr
      cases hnr
    · rw [hnotSelf] at hself
      cases hself
  have hhit :
      (final,
          restrictBnd queryVars
            (((restrictBnd queryVars
                ((Bindings.merge partBnd p.2).head?.getD p.2)).merge
                finalBnd).head?.getD finalBnd)) ∈
        (mettaEvalExprRootFoldStep env fuel queryVars w partBnd returnAtom
          accPre p).1 := by
    unfold mettaEvalExprRootFoldStep
    split
    · rename_i hbranch
      exact False.elim (hfirst hbranch)
    · split
      · rename_i hbranch
        have hret : returnAtom = true := hbranch
        rw [hReturns] at hret
        cases hret
      · exact List.mem_append.mpr
          (Or.inr (List.mem_map.mpr
            ⟨(final, finalBnd), hFinal accPre.2, rfl⟩))
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
    match (part.1.zip args).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) with
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
    (hnoerr : (part.1.zip args).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none)
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
    (hnoerr : (part.1.zip args).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none)
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
    (hnoerr : (part.1.zip args).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none)
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
    (hnoerr : (part.1.zip args).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none)
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
runtime error results.  The selected constructor carries the complete runtime decision; masks and
return policies are derived projections rather than lossy indices. -/
inductive ExactApplicationPolicy (env : MinEnv) (world : World) (op : String)
    (args : List Atom) : Type where
  | selected (selected : SelectedFunctionType)
      (hSelected : selectFunctionType env world (.sym op) args = .selected selected) :
      ExactApplicationPolicy env world op args
  | untypedTuple
      (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true) :
      ExactApplicationPolicy env world op args

/-- Selected-policy payload implementing untyped tuple fallback. -/
def untypedTupleSelectedType (arity : Nat) : SelectedFunctionType :=
  ⟨.sym "%Undefined%", List.replicate arity (.sym "%Undefined%"),
    .sym "%Undefined%", []⟩

/-- Tuple-fallback payload carrying the live theory used by the shared
application plan. -/
def untypedTupleSelectedTypeFrom (incoming : Bindings)
    (arity : Nat) : SelectedFunctionType :=
  ⟨.sym "%Undefined%", List.replicate arity (.sym "%Undefined%"),
    .sym "%Undefined%", incoming⟩

/-- Every tuple-fallback argument is evaluated under the neutral expected type. -/
theorem argumentEvaluationPolicies_untypedTuple (arity : Nat) :
    argumentEvaluationPolicies (untypedTupleSelectedType arity) arity =
      List.replicate arity (true, Atom.sym "%Undefined%") := by
  apply List.ext_get
  · simp [argumentEvaluationPolicies]
  · intro i _ hright
    have hi : i < arity := by simpa using hright
    simp [argumentEvaluationPolicies, untypedTupleSelectedType,
      List.getElem?_replicate, hi, instantiate_nil]
    decide

@[simp] theorem returnsAtom_untypedTuple (arity : Nat) :
    Metta.Minimal.returnsAtom (untypedTupleSelectedType arity) = false := by
  simp [Metta.Minimal.returnsAtom, untypedTupleSelectedType, instantiate_nil]
  decide

@[simp] theorem selectedResultExpected_untypedTuple (arity : Nat) :
    selectedResultExpected (untypedTupleSelectedType arity) = .sym "%Undefined%" := by
  simp [selectedResultExpected, untypedTupleSelectedType, instantiate_nil]

/-- Complete selected-policy payload used by the evaluator.  Tuple fallback is represented by the
all-`%Undefined%` policy that is definitionally ordinary evaluation at every recursive call. -/
def ExactApplicationPolicy.selectedType {env : MinEnv} {world : World} {op : String}
    {args : List Atom} (policy : ExactApplicationPolicy env world op args) : SelectedFunctionType :=
  match policy with
  | .selected choice _ => choice
  | .untypedTuple _ => untypedTupleSelectedType args.length

/-- Complete policy payload as executed from a live incoming theory.  Selected
arrows already carry their applicability theory; tuple fallback carries the
incoming theory explicitly. -/
def ExactApplicationPolicy.selectedTypeFrom
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (incoming : Bindings)
    (policy : ExactApplicationPolicy env world op args) : SelectedFunctionType :=
  match policy with
  | .selected choice _ => choice
  | .untypedTuple _ => untypedTupleSelectedTypeFrom incoming args.length

/-- Argument-evaluation mask derived from the complete runtime decision. -/
def ExactApplicationPolicy.argumentMask {env : MinEnv} {world : World} {op : String}
    {args : List Atom} (policy : ExactApplicationPolicy env world op args) : List Bool :=
  Metta.Minimal.argMask policy.selectedType args.length

/-- Result-quotation policy derived from the complete runtime decision. -/
def ExactApplicationPolicy.returnIsAtom {env : MinEnv} {world : World} {op : String}
    {args : List Atom} (policy : ExactApplicationPolicy env world op args) : Bool :=
  Metta.Minimal.returnsAtom policy.selectedType

/-- The live-theory scan result that must correspond to one raw application
policy when ordinary evaluation enters the shared selected-application plan. -/
def ExactApplicationPolicy.planScanOutcome
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (policy : ExactApplicationPolicy env world op args) :
    ExpectedFunctionTypeScanOutcome :=
  match policy with
  | .selected choice _ .. => .selected choice
  | .untypedTuple _ .. => .exhausted [] true

/-- Operator-head evaluation and public seeding required by a selected raw
policy.  Tuple fallback has no selected arrow and therefore no head-cast
obligation. -/
def ExactApplicationPolicy.headSeedCorresponds
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (incoming : Bindings)
    (policy : ExactApplicationPolicy env world op args) : Prop :=
  match policy with
  | .selected choice _ .. =>
      ∃ headBindings,
        mettaTypeCastAvoiding
            (expectedApplicationVisibleScope
              (.expr (.sym op :: args)) (.sym "%Undefined%"))
            env world choice.typeBindings (.sym op) choice.functionType =
          .inr headBindings ∧
        selectedApplicationInitialBindingsFromTheory incoming
            (.expr (.sym op :: args)) (.sym "%Undefined%") headBindings =
          [incoming]
  | .untypedTuple _ .. => True

/-- The data selected by the repaired ordinary application entry point from a
live evaluator theory.  This is intentionally not indexed by the legacy raw
selector: seeding applicability with `incoming` can extend the selected type
theory, and capture-avoiding signature localization can change its private
spelling.  Consumers that need a particular mask or result policy prove those
properties separately about `selected`. -/
structure SelectedApplicationExecutionPlan
    (env : MinEnv) (world : World) (incoming : Bindings)
    (op : String) (args : List Atom) : Type where
  selected : SelectedFunctionType
  scan :
    selectFunctionTypeForExpectedFrom env world (.sym op) args
        (.sym "%Undefined%") incoming = .selected selected
  headBindings : Bindings
  headCast :
    mettaTypeCastAvoiding
        (expectedApplicationVisibleScope
          (.expr (.sym op :: args)) (.sym "%Undefined%"))
        env world selected.typeBindings (.sym op) selected.functionType =
      .inr headBindings

/-- Public seeds emitted by one live selected plan after operator-head
checking.  Keeping this as derived data prevents a proof carrier from silently
assuming singleton or binding-neutral applicability. -/
def SelectedApplicationExecutionPlan.seeds
    {env : MinEnv} {world : World} {incoming : Bindings}
    {op : String} {args : List Atom}
    (plan : SelectedApplicationExecutionPlan env world incoming op args) :
    List Bindings :=
  selectedApplicationInitialBindingsFromTheory incoming
    (.expr (.sym op :: args)) (.sym "%Undefined%") plan.headBindings

/-- Evidence that one raw policy is exactly the policy executed by the shared
ordinary selected-application plan from `incoming`.  This is deliberately a
consumer-side layer over `ExactApplicationPolicy`: typed consumers share the
raw decision without being forced to claim head/seed neutrality. -/
structure ApplicationPlanCorresponds
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (incoming : Bindings)
    (policy : ExactApplicationPolicy env world op args) : Prop where
  scan :
    selectFunctionTypeForExpectedFrom env world (.sym op) args
        (.sym "%Undefined%") incoming = policy.planScanOutcome
  headSeed : policy.headSeedCorresponds incoming

/-- Recover raw-policy correspondence when a live selected plan is also the
exact raw empty/compatibility selection.  The equality is supplied explicitly:
for nonempty incoming theories it is generally false, so this conversion can
never silently erase the seeded-scan distinction. -/
def SelectedApplicationExecutionPlan.toApplicationPlanCorresponds
    {env : MinEnv} {world : World} {incoming : Bindings}
    {op : String} {args : List Atom}
    (plan : SelectedApplicationExecutionPlan env world incoming op args)
    (hRaw : selectFunctionType env world (.sym op) args =
      .selected plan.selected)
    (hSeed : plan.seeds = [incoming]) :
    ApplicationPlanCorresponds incoming (.selected plan.selected hRaw) := by
  constructor
  · simpa [ExactApplicationPolicy.planScanOutcome] using plan.scan
  · simp only [ExactApplicationPolicy.headSeedCorresponds]
    exact ⟨plan.headBindings, plan.headCast, hSeed⟩

/-- Build selected-plan evidence from the three observable equations that the
shared application pipeline consumes.  The raw scan remains part of
`ExactApplicationPolicy`; this constructor supplies only the live expected
scan, operator-head cast, and public seed equation. -/
def ApplicationPlanCorresponds.ofSelected
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    {incoming : Bindings} {selected : SelectedFunctionType}
    {hSelected : selectFunctionType env world (.sym op) args = .selected selected}
    (hLiveScan :
      selectFunctionTypeForExpectedFrom env world (.sym op) args
          (.sym "%Undefined%") incoming = .selected selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope
        (.expr (.sym op :: args)) (.sym "%Undefined%"))
      env world selected.typeBindings (.sym op) selected.functionType =
        .inr headBindings)
    (hSeed : selectedApplicationInitialBindingsFromTheory incoming
      (.expr (.sym op :: args)) (.sym "%Undefined%") headBindings =
        [incoming]) :
    ApplicationPlanCorresponds incoming (.selected selected hSelected) := by
  constructor
  · simpa [ExactApplicationPolicy.planScanOutcome] using hLiveScan
  · simp only [ExactApplicationPolicy.headSeedCorresponds]
    exact ⟨headBindings, hHead, hSeed⟩

/-- Build tuple-fallback plan evidence from the exact live expected scan. -/
def ApplicationPlanCorresponds.ofUntypedTuple
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    {incoming : Bindings}
    {hScan : selectFunctionType env world (.sym op) args = .exhausted [] true}
    (hLiveScan :
      selectFunctionTypeForExpectedFrom env world (.sym op) args
          (.sym "%Undefined%") incoming = .exhausted [] true) :
    ApplicationPlanCorresponds incoming (.untypedTuple hScan) := by
  constructor
  · simpa [ExactApplicationPolicy.planScanOutcome] using hLiveScan
  · trivial

/-- A singleton non-arrow `%Undefined%` type candidate is exactly the untyped
tuple fallback in the live expected scan with empty incoming bindings.  The
statement preserves the ordered scan result, including its empty error block
and tuple-eligibility bit. -/
theorem selectFunctionTypeForExpectedFrom_undefined_exhausted
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (hTypes : getTypes env (typePrep world (.sym op)) = [.sym "%Undefined%"]) :
    selectFunctionTypeForExpectedFrom env world (.sym op) args
        (.sym "%Undefined%") [] = .exhausted [] true := by
  simp [selectFunctionTypeForExpectedFrom,
    freshenFunctionTypeCandidatesAvoiding, hTypes, freshenTypeCandidate,
    renameAllVars, scanFunctionTypeCandidatesForExpectedFrom,
    ExpectedFunctionTypeScanOutcome.markTupleEligible]

/-- Live-theory form of `selectFunctionTypeForExpectedFrom_undefined_exhausted`.

A singleton non-arrow `%Undefined%` candidate contributes no applicability bindings, so the
incoming theory cannot turn it into an arrow or an error.  Tuple eligibility is therefore exact
for every incoming binding state, not only the empty seed. -/
theorem selectFunctionTypeForExpectedFrom_undefined_exhausted_from
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (incoming : Bindings)
    (hTypes : getTypes env (typePrep world (.sym op)) = [.sym "%Undefined%"]) :
    selectFunctionTypeForExpectedFrom env world (.sym op) args
        (.sym "%Undefined%") incoming = .exhausted [] true := by
  simp [selectFunctionTypeForExpectedFrom,
    freshenFunctionTypeCandidatesAvoiding, hTypes, freshenTypeCandidate,
    renameAllVars, scanFunctionTypeCandidatesForExpectedFrom,
    ExpectedFunctionTypeScanOutcome.markTupleEligible]

/-- The Boolean compatibility mask is exactly the first projection of the complete argument
policies. -/
theorem argumentEvaluationPolicies_map_fst (selected : SelectedFunctionType) (arity : Nat) :
    (argumentEvaluationPolicies selected arity).map Prod.fst =
      argMask selected arity := by
  simp [argumentEvaluationPolicies, argMask, List.map_map, Function.comp_def]
  intro i hi
  split <;> rfl

/-- A checked Boolean projection of the data-bearing application decision.  This is the uniform
carrier for concrete operator suppliers: typed and recursion-neutral consumers share the same
runtime decision, while any claim that expected-aware recursion is inert remains a separate proof
obligation. -/
structure ApplicationPolicyProjection
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool) : Type where
  decision : ExactApplicationPolicy env world op args
  argumentMask_eq : decision.argumentMask = mask
  returnIsAtom_eq : decision.returnIsAtom = returnAtom

/-- The result-quotation fact exposed in the executable vocabulary consumed by application
evaluators.  Downstream proofs use this characterization instead of unfolding the derived
`ExactApplicationPolicy.returnIsAtom` projection. -/
theorem ApplicationPolicyProjection.returnsAtom_selectedType_eq
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    {mask : List Bool} {returnAtom : Bool}
    (policy : ApplicationPolicyProjection env world op args mask returnAtom) :
    returnsAtom policy.decision.selectedType = returnAtom := by
  exact policy.returnIsAtom_eq

def ApplicationPolicyProjection.selected
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env world (.sym op) args = .selected selected) :
    ApplicationPolicyProjection env world op args
      (argMask selected args.length) (returnsAtom selected) :=
  ⟨.selected selected hSelected, rfl, rfl⟩

def ApplicationPolicyProjection.untypedTuple
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
  (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true) :
    ApplicationPolicyProjection env world op args
      (List.replicate args.length true) false :=
  ⟨.untypedTuple hScan, by
      change argMask (untypedTupleSelectedType args.length) args.length =
        List.replicate args.length true
      rw [← argumentEvaluationPolicies_map_fst,
        argumentEvaluationPolicies_untypedTuple]
      simp,
    returnsAtom_untypedTuple args.length⟩

/-- Exact typed shape for a lazy ternary application: evaluate the condition under `expected`,
quote both branches as `Atom`, and recurse on results under `%Undefined%`.  The raw runtime
decision remains the sole data source; this wrapper adds only checked facts about that decision. -/
structure EvalQuotedQuotedApplicationPolicy
    (env : MinEnv) (world : World) (op : String)
    (args : List Atom) (expected : Atom) : Type where
  raw : ApplicationPolicyProjection env world op args
    [true, false, false] false
  selected_eq :
    selectFunctionType env world (.sym op) args =
      .selected raw.decision.selectedType
  argumentPolicies_eq :
    argumentEvaluationPolicies raw.decision.selectedType 3 =
      [(true, expected), (false, .sym "Atom"), (false, .sym "Atom")]
  resultExpected_eq :
    selectedResultExpected raw.decision.selectedType = .sym "%Undefined%"

/-- Forget the checked expected-type shape while retaining the authoritative runtime decision. -/
def EvalQuotedQuotedApplicationPolicy.toProjection
    {env : MinEnv} {world : World} {op : String}
    {args : List Atom} {expected : Atom}
    (policy : EvalQuotedQuotedApplicationPolicy env world op
      args expected) :
    ApplicationPolicyProjection env world op args
      [true, false, false] false :=
  policy.raw

/-- Exact typed shape for an application whose arguments are all quoted `Atom`s and whose
recursively checked result is `Bool`.  This is intentionally not recursion-neutral: the result
cast is semantic, and is discharged only by concrete Boolean-frontier equations. -/
structure QuotedBoolApplicationPolicy
    (env : MinEnv) (world : World) (op : String) (args : List Atom) : Type where
  decision : ExactApplicationPolicy env world op args
  selected_eq :
    selectFunctionType env world (.sym op) args =
      .selected decision.selectedType
  argumentPolicies_eq :
    argumentEvaluationPolicies decision.selectedType args.length =
      List.replicate args.length (false, .sym "Atom")
  returnIsAtom_eq : decision.returnIsAtom = false
  resultExpected_eq :
    selectedResultExpected decision.selectedType = .sym "Bool"

/-- Live selected-plan evidence for a typed lazy ternary consumer.  All shape
facts are stated about the payload that the seeded selector actually returned;
no equality with the raw empty-seed selector is assumed. -/
structure EvalQuotedQuotedApplicationExecutionPlan
    (env : MinEnv) (world : World) (incoming : Bindings)
    (op : String) (args : List Atom) (expected : Atom) : Type where
  plan : SelectedApplicationExecutionPlan env world incoming op args
  seedSingleton : plan.seeds = [incoming]
  argumentPolicies_eq :
    argumentEvaluationPolicies plan.selected args.length =
      [(true, expected), (false, .sym "Atom"), (false, .sym "Atom")]
  returnIsAtom_eq : returnsAtom plan.selected = false
  resultExpected_eq : selectedResultExpected plan.selected = .sym "%Undefined%"

/-- A quoted-argument/Boolean-result policy never returns its result as a quoted `Atom`. -/
theorem QuotedBoolApplicationPolicy.returnsAtom_selectedType_eq
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (policy : QuotedBoolApplicationPolicy env world op args) :
    returnsAtom policy.decision.selectedType = false := by
  exact policy.returnIsAtom_eq

/-- Forget the checked quoted-argument/Boolean-result shape while retaining the authoritative
runtime decision. -/
def QuotedBoolApplicationPolicy.toProjection
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (policy : QuotedBoolApplicationPolicy env world op args) :
    ApplicationPolicyProjection env world op args
      (List.replicate args.length false) false := by
  refine ⟨policy.decision, ?_, policy.returnIsAtom_eq⟩
  change argMask policy.decision.selectedType args.length =
    List.replicate args.length false
  rw [← argumentEvaluationPolicies_map_fst,
    policy.argumentPolicies_eq]
  simp

/-- `%Undefined%` is the neutral expected-type policy used by ordinary recursive evaluation. -/
theorem mettaEvalExpected_undefined (env : MinEnv) (fuel : Nat) (st : St)
    (bnd : Bindings) (atom : Atom) :
    mettaEvalExpected env fuel st bnd atom (.sym "%Undefined%") =
      mettaEval env fuel st bnd atom := by
  unfold mettaEvalExpected
  rfl

/-- Expected-aware evaluation preserves a grounded Boolean exactly when its concrete type cast is
binding-neutral and the ordinary reduction frontier reports `NotReducible`.  The hypotheses are
equations rather than a broad irreducibility predicate: they pin the entry cast and the recursive
frontier that could otherwise change the evaluation path. -/
theorem mettaEvalExpected_bool_of_notReducible
    (env : MinEnv) (fuel : Nat) (st : St) (b : Bool) (expected : Atom)
    (hExpected : (expected == .sym "%Undefined%") = false)
    (hCast : mettaTypeCast env st.world [] (.gnd (.bool b)) expected = .inr [])
    (hReduce :
      interpretFuel env (fuel + 1) st
          [{ stack := atomToStack (.expr [.sym "eval", .gnd (.bool b)]) [], bnd := [] }] [] =
        ([(notReducibleA, [])], st)) :
    mettaEvalExpected env (fuel + 1) st [] (.gnd (.bool b)) expected =
      ([((.gnd (.bool b)), [])], st) := by
  have _ := hReduce
  rw [mettaEvalExpected]
  rw [hExpected]
  simp only [Bool.false_eq_true, ↓reduceIte, Metta.instantiate_nil]
  by_cases hPass :
      (expected == Atom.atomType ||
        expected == Atom.typeAtomOfMetaType (Atom.gnd (.bool b)).metaType ||
        (Atom.gnd (.bool b)).metaType == MetaType.variable) = true
  · simp [hPass]
  · simp only [hPass, Bool.false_eq_true, ↓reduceIte]
    rw [hCast]
    simp [Metta.instantiate]

/-- Sufficient and explicit conditions under which expected-aware recursion coincides with the
legacy mask-only executor.  Quoted arguments may carry non-neutral expected types because neither
executor recursively evaluates them. -/
structure SelectedApplicationRecursionNeutral
    (selected : SelectedFunctionType) (arity : Nat) : Prop where
  argumentExpected :
    ∀ policy ∈ argumentEvaluationPolicies selected arity,
      policy.1 = true → policy.2 = Atom.sym "%Undefined%"
  resultExpected :
    returnsAtom selected = false →
      selectedResultExpected selected = Atom.sym "%Undefined%"

/-- A checked compatibility view for consumers whose theorem statements still use a Boolean mask
and return flag.  The data-bearing runtime decision remains authoritative; the indexed values are
accepted only together with projection equalities and a proof that expected-aware recursion is
neutral at this application. -/
structure RecursionNeutralApplicationPolicy
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool) : Type where
  decision : ExactApplicationPolicy env world op args
  planCorresponds : ApplicationPlanCorresponds [] decision
  recursionNeutral :
    SelectedApplicationRecursionNeutral decision.selectedType args.length
  argumentMask_eq : decision.argumentMask = mask
  returnIsAtom_eq : decision.returnIsAtom = returnAtom

/-- Live selected-plan view for compatibility consumers whose recursive
expected types are genuinely neutral.  The raw selector remains useful for
empty callers; nonempty callers carry this structure instead. -/
structure RecursionNeutralApplicationExecutionPlan
    (env : MinEnv) (world : World) (incoming : Bindings)
    (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool) : Type where
  plan : SelectedApplicationExecutionPlan env world incoming op args
  seedSingleton : plan.seeds = [incoming]
  recursionNeutral :
    SelectedApplicationRecursionNeutral plan.selected args.length
  argumentMask_eq : argMask plan.selected args.length = mask
  returnIsAtom_eq : returnsAtom plan.selected = returnAtom

/-- Promote the one authoritative runtime decision to the compatibility layer exactly when its
expected-aware recursive calls are proved inert. No selected data or projection facts are
recomputed. -/
def ApplicationPolicyProjection.withRecursionNeutral
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    {mask : List Bool} {returnAtom : Bool}
    (policy : ApplicationPolicyProjection env world op args mask returnAtom)
    (planCorresponds : ApplicationPlanCorresponds [] policy.decision)
    (hNeutral : SelectedApplicationRecursionNeutral
      policy.decision.selectedType args.length) :
    RecursionNeutralApplicationPolicy env world op args mask returnAtom :=
  ⟨policy.decision, planCorresponds, hNeutral,
    policy.argumentMask_eq, policy.returnIsAtom_eq⟩

/-- Untyped tuple fallback is recursion-neutral at every arity: every recursive argument call and
the result cast use `%Undefined%`. -/
theorem selectedApplicationRecursionNeutral_untypedTuple (arity : Nat) :
    SelectedApplicationRecursionNeutral (untypedTupleSelectedType arity) arity := by
  constructor
  · intro policy hmem _
    rw [argumentEvaluationPolicies_untypedTuple] at hmem
    have hp : arity ≠ 0 ∧ policy = (true, Atom.sym "%Undefined%") := by
      simpa using hmem
    rw [hp.2]
  · intro _
    exact selectedResultExpected_untypedTuple arity

/-- A selected application with no recursively evaluated arguments is recursion-neutral whenever
its result is quoted as `Atom` or is recursively checked only against `%Undefined%`. -/
theorem selectedApplicationRecursionNeutral_of_all_arguments_quoted
    (selected : SelectedFunctionType) (arity : Nat)
    (hMask : argMask selected arity = List.replicate arity false)
    (hResult : returnsAtom selected = true ∨
      selectedResultExpected selected = Atom.sym "%Undefined%") :
    SelectedApplicationRecursionNeutral selected arity := by
  constructor
  · intro policy hmem hEval
    have hfst : policy.1 ∈
        (argumentEvaluationPolicies selected arity).map Prod.fst :=
      List.mem_map_of_mem hmem
    rw [argumentEvaluationPolicies_map_fst, hMask] at hfst
    simp at hfst
    simp [hfst.2] at hEval
  · intro hNotQuoted
    rcases hResult with hQuoted | hUndefined
    · rw [hQuoted] at hNotQuoted
      contradiction
    · exact hUndefined

/-- Promote an all-quoted checked projection without rebuilding its runtime decision. -/
def ApplicationPolicyProjection.withRecursionNeutralOfAllArgumentsQuoted
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    {mask : List Bool} {returnAtom : Bool}
    (policy : ApplicationPolicyProjection env world op args mask returnAtom)
    (planCorresponds : ApplicationPlanCorresponds [] policy.decision)
    (hMask : mask = List.replicate args.length false)
    (hResult : returnAtom = true ∨
      selectedResultExpected policy.decision.selectedType = Atom.sym "%Undefined%") :
    RecursionNeutralApplicationPolicy env world op args mask returnAtom :=
  policy.withRecursionNeutral planCorresponds
    (selectedApplicationRecursionNeutral_of_all_arguments_quoted
      policy.decision.selectedType args.length
      (policy.argumentMask_eq.trans hMask)
      (hResult.imp (policy.returnIsAtom_eq.trans ·) id))

/-- Checked recursion-neutral view of the single-source untyped-tuple projection. -/
def ApplicationPolicyProjection.untypedTupleWithRecursionNeutral
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true)
    (planCorresponds : ApplicationPlanCorresponds [] (.untypedTuple hScan)) :
    RecursionNeutralApplicationPolicy env world op args
      (List.replicate args.length true) false :=
  (ApplicationPolicyProjection.untypedTuple hScan).withRecursionNeutral
    planCorresponds
    (selectedApplicationRecursionNeutral_untypedTuple args.length)

private def expectedArgumentFoldStep
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom)
    (acc : List (List Atom × Bindings) × St)
    (ae : Atom × (Bool × Atom)) :
    List (List Atom × Bindings) × St :=
  acc.1.foldl (fun (acc2 : List (List Atom × Bindings) × St) part =>
    match (part.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
    | some _ => (acc2.1 ++ [part], acc2.2)
    | none =>
        if ae.2.1 then
          let (results, st') := evalRecursive acc2.2 part.2 ae.1 ae.2.2
          (acc2.1 ++ results.map (fun result =>
            (part.1 ++ [result.1], restrictBnd queryVars
              ((Bindings.merge part.2 result.2).head?.getD result.2))), st')
        else
          (acc2.1 ++ [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2))
    ([], acc.2)

def selectedArgumentFoldStep
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom)
    (acc : List (List Atom × Bindings) × St)
    (ae : Atom × Bool) :
    List (List Atom × Bindings) × St :=
  acc.1.foldl (fun (acc2 : List (List Atom × Bindings) × St) part =>
    match (part.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
    | some _ => (acc2.1 ++ [part], acc2.2)
    | none =>
        if ae.2 then
          let (results, st') := evalRecursive acc2.2 part.2 ae.1
          (acc2.1 ++ results.map (fun result =>
            (part.1 ++ [result.1], restrictBnd queryVars
              ((Bindings.merge part.2 result.2).head?.getD result.2))), st')
        else
          (acc2.1 ++ [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2))
    ([], acc.2)

/-- The inner worker for one recursively evaluated argument.  Naming this
step exposes the state-neutral changed-error branch without tying proofs to a
particular application arity. -/
def evaluatedArgumentPartFoldStep
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom) (argument : Atom)
    (acc : List (List Atom × Bindings) × St)
    (part : List Atom × Bindings) :
    List (List Atom × Bindings) × St :=
  match (part.1.zip source).find?
      (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | some _ => (acc.1 ++ [part], acc.2)
  | none =>
      let (results, st') := evalRecursive acc.2 part.2 argument
      (acc.1 ++ results.map (fun result =>
        (part.1 ++ [result.1], restrictBnd queryVars
          ((Bindings.merge part.2 result.2).head?.getD result.2))), st')

/-- The `true` arm of the selected argument worker is exactly the named
evaluated-part fold. -/
theorem selectedArgumentFoldStep_true_eq_evaluatedArgumentPartFold
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom)
    (rows : List (List Atom × Bindings)) (st : St) (argument : Atom) :
    selectedArgumentFoldStep evalRecursive queryVars source (rows, st)
        (argument, true) =
      rows.foldl
        (evaluatedArgumentPartFoldStep evalRecursive queryVars source argument)
        ([], st) := by
  rfl

/-- A recursively evaluated argument preserves any state invariant when each
actually evaluated row preserves it.  Rows stopped by a changed error retain
the accumulator state and therefore require no recursive-call premise. -/
theorem evaluatedArgumentPartFold_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom) (argument : Atom)
    (parts : List (List Atom × Bindings))
    (acc : List (List Atom × Bindings) × St) (P : St → Prop)
    (hinit : P acc.2)
    (hstep :
      ∀ (acc0 : List (List Atom × Bindings) × St)
        (part : List Atom × Bindings),
        part ∈ parts →
          ((part.1.zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none →
          P acc0.2 → P (evalRecursive acc0.2 part.2 argument).2) :
    P (parts.foldl
      (evaluatedArgumentPartFoldStep evalRecursive queryVars source argument)
      acc).2 := by
  induction parts generalizing acc with
  | nil => simpa using hinit
  | cons part rest ih =>
      have hstepRest :
          ∀ (acc0 : List (List Atom × Bindings) × St)
            (part' : List Atom × Bindings),
            part' ∈ rest →
              ((part'.1.zip source).find?
                (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none →
              P acc0.2 → P (evalRecursive acc0.2 part'.2 argument).2 := by
        intro acc0 part' hmem hclean hP
        exact hstep acc0 part' (by simp [hmem]) hclean hP
      have hnext :
          P (evaluatedArgumentPartFoldStep evalRecursive queryVars source
            argument acc part).2 := by
        cases hChanged :
            (part.1.zip source).find?
              (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
        | some changed =>
            simpa [evaluatedArgumentPartFoldStep, hChanged] using hinit
        | none =>
            simpa [evaluatedArgumentPartFoldStep, hChanged] using
              hstep acc part (by simp) hChanged hinit
      exact ih
        (acc := evaluatedArgumentPartFoldStep evalRecursive queryVars source
          argument acc part)
        hnext hstepRest

/-- Folding one evaluated argument preserves the invariant that every clean
output row is exactly one atom longer than its source row.  Stopped rows are
excluded by the clean-output premise itself. -/
theorem evaluatedArgumentPartFold_preserves_clean_length
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom) (argument : Atom)
    (parts : List (List Atom × Bindings))
    (acc : List (List Atom × Bindings) × St) (length : Nat)
    (hacc : ∀ row ∈ acc.1,
      ((row.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none →
      row.1.length = length + 1)
    (hparts : ∀ part ∈ parts, part.1.length = length) :
    ∀ row ∈
        (parts.foldl
          (evaluatedArgumentPartFoldStep evalRecursive queryVars source argument)
          acc).1,
      ((row.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none →
      row.1.length = length + 1 := by
  induction parts generalizing acc with
  | nil => simpa using hacc
  | cons part rest ih =>
      have hpartsRest : ∀ part' ∈ rest, part'.1.length = length := by
        intro part' hmem
        exact hparts part' (by simp [hmem])
      apply ih
        (acc := evaluatedArgumentPartFoldStep evalRecursive queryVars source
          argument acc part)
        (hparts := hpartsRest)
      intro row hrow hclean
      cases hChanged :
          (part.1.zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
      | some changed =>
          have hrow' : row ∈ acc.1 ++ [part] := by
            simpa [evaluatedArgumentPartFoldStep, hChanged] using hrow
          rcases List.mem_append.mp hrow' with hold | hnew
          · exact hacc row hold hclean
          · have : row = part := by simpa using hnew
            subst row
            rw [hChanged] at hclean
            contradiction
      | none =>
          cases hEval : evalRecursive acc.2 part.2 argument with
          | mk results st' =>
              have hrow' :
                  row ∈ acc.1 ++ results.map (fun result =>
                    (part.1 ++ [result.1], restrictBnd queryVars
                      ((Bindings.merge part.2 result.2).head?.getD result.2))) := by
                simpa [evaluatedArgumentPartFoldStep, hChanged, hEval] using hrow
              rcases List.mem_append.mp hrow' with hold | hnew
              · exact hacc row hold hclean
              · rcases List.mem_map.mp hnew with ⟨result, _, rfl⟩
                simp [hparts part (by simp)]

/-- Empty-output specialization of
`evaluatedArgumentPartFold_preserves_clean_length`. -/
theorem evaluatedArgumentPartFold_clean_mem_length
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom) (argument : Atom)
    (parts : List (List Atom × Bindings)) (st : St) (length : Nat)
    (hparts : ∀ part ∈ parts, part.1.length = length)
    (row : List Atom × Bindings)
    (hmem : row ∈
      (parts.foldl
        (evaluatedArgumentPartFoldStep evalRecursive queryVars source argument)
        ([], st)).1)
    (hclean :
      ((row.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    row.1.length = length + 1 := by
  exact evaluatedArgumentPartFold_preserves_clean_length
    evalRecursive queryVars source argument parts ([], st) length
    (by simp) hparts row hmem hclean

/-- Zipping a longer evaluated-argument list against the same source list preserves
the already evaluated prefix.  This is the structural fact needed to transport the
worker's final "no changed error" observation back to every earlier argument step. -/
private theorem zip_append_left_prefix
    (evaluatedPrefix suffix source : List Atom) :
    evaluatedPrefix.zip source <+:
      (evaluatedPrefix ++ suffix).zip source := by
  induction evaluatedPrefix generalizing source with
  | nil =>
      exact ⟨suffix.zip source, by simp⟩
  | cons evaluated tailPrefix ih =>
      cases source with
      | nil => exact ⟨[], by simp⟩
      | cons original source =>
          rcases ih source with ⟨tail, htail⟩
          exact ⟨tail, by
            simpa using congrArg (List.cons (evaluated, original)) htail⟩

/-- If a completed argument row contains no changed terminal result, neither does any
already evaluated prefix.  This is the chronology boundary exposed by the
early-stop application workers. -/
theorem changedArgumentStop_prefix_none
    (evaluatedPrefix suffix source : List Atom)
    (hNoError :
      (((evaluatedPrefix ++ suffix).zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    ((evaluatedPrefix.zip source).find?
      (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none :=
  (zip_append_left_prefix evaluatedPrefix suffix source).find?_eq_none hNoError

/-- A row whose evaluated atoms are neither `Empty` nor errors has no changed
argument stop, independently of atom equality.  This deliberately uses only
the left projection of the zip: `Atom`'s executable equality is not lawful for
all grounded values, while the worker guard short-circuits on the terminal
classification. -/
theorem firstChangedArgumentStop_eq_none_of_forall_fst_not_isEmptyOrError
    (xs ys : List Atom)
    (h : ∀ x ∈ xs, (x == emptyA || x.isError) = false) :
    firstChangedArgumentStop xs ys = none := by
  unfold firstChangedArgumentStop
  apply List.find?_eq_none.mpr
  intro pair hpair
  have hfst : pair.1 ∈ xs := (List.of_mem_zip hpair).1
  simp [h pair.1 hfst]

/-- A row has no changed terminal result when every aligned pair is either
nonterminal on the evaluated side or unchanged.  Unlike a blanket
reflexivity argument, this statement remains valid for `Atom`'s non-lawful
executable equality because equality evidence is supplied only for the pairs
that need it. -/
theorem firstChangedArgumentStop_eq_none_of_forall_pair
    (xs ys : List Atom)
    (h : ∀ pair ∈ xs.zip ys,
      (pair.1 == emptyA || pair.1.isError) = false ∨
        (pair.1 != pair.2) = false) :
    firstChangedArgumentStop xs ys = none := by
  unfold firstChangedArgumentStop
  apply List.find?_eq_none.mpr
  intro pair hpair
  rcases h pair hpair with hterminal | hsame
  · simp [hterminal]
  · simp [hsame]

/-- Comparison with the distinguished `Empty` symbol is lawful even though
`Atom` equality is not lawful for arbitrary grounded floats. -/
theorem beq_empty_eq_true_iff (atom : Atom) :
    (atom == emptyA) = true ↔ atom = emptyA := by
  change (atom == Atom.sym "Empty") = true ↔ atom = Atom.sym "Empty"
  cases atom with
  | sym name =>
      change
        (Atom.beq (Atom.sym name) (Atom.sym "Empty")) = true ↔
          Atom.sym name = Atom.sym "Empty"
      simp [Atom.beq]
  | var name =>
      change (Atom.beq (Atom.var name) (Atom.sym "Empty")) = true ↔ _
      simp [Atom.beq]
  | gnd value =>
      change (Atom.beq (Atom.gnd value) (Atom.sym "Empty")) = true ↔ _
      simp [Atom.beq]
  | expr atoms =>
      change (Atom.beq (Atom.expr atoms) (Atom.sym "Empty")) = true ↔ _
      simp [Atom.beq]

/-- Constructor-disjoint comparisons with `Empty`.  These are deliberately
separate from any blanket reflexivity law for `Atom`: grounded equality may be
non-lawful internally, but no variable, grounded atom, or expression can be
the distinguished symbol constructor. -/
@[simp] theorem atom_var_beq_empty_false (name : String) :
    (Atom.var name == emptyA) = false := rfl

@[simp] theorem atom_gnd_beq_empty_false (value : Ground) :
    (Atom.gnd value == emptyA) = false := rfl

@[simp] theorem atom_expr_beq_empty_false (atoms : List Atom) :
    (Atom.expr atoms == emptyA) = false := rfl

/-- Comparison with `Empty` supplies the one self-equality fact needed by the
early-stop guard, without asserting reflexivity for arbitrary grounded atoms. -/
@[simp] theorem beq_empty_eq_true_implies_ne_self_eq_false (atom : Atom) :
    (atom == emptyA) = true → (atom != atom) = false := by
  intro hEmpty
  have hatom : atom = emptyA := (beq_empty_eq_true_iff atom).mp hEmpty
  subst atom
  rfl

/-- Proposition-normalized form of
`beq_empty_eq_true_implies_ne_self_eq_false`.  Evaluator simplification turns a
Boolean terminal guard into this implication after learning that an aligned
atom is not an error; registering the whole proposition, rather than its
consequent, lets simplification close that branch without requiring lawful
equality for every grounded atom. -/
@[simp] theorem beq_empty_true_imp_ne_self_false_iff_true (atom : Atom) :
    ((atom == emptyA) = true → (atom != atom) = false) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact beq_empty_eq_true_implies_ne_self_eq_false atom

/-- Boolean normal form of the same `Empty` self-alignment fact.  This is the
shape left by evaluator reduction after an `isError = false` hypothesis has
already removed the error disjunct. -/
@[simp] theorem beq_empty_and_ne_self_eq_false (atom : Atom) :
    ((atom == emptyA) && atom != atom) = false := by
  cases hEmpty : (atom == emptyA) with
  | false => rfl
  | true =>
      have hatom : atom = emptyA := (beq_empty_eq_true_iff atom).mp hEmpty
      subst atom
      rfl

/-- An atom that is not an error cannot be a changed terminal result when it
is aligned with itself.  The statement remains valid without a global
`LawfulBEq Atom`: if the atom compares equal to `Empty`, the dedicated lawful
comparison identifies it propositionally with `Empty`; otherwise the terminal
test is already false. -/
@[simp] theorem changedArgumentStop_self_eq_false_of_not_error
    (atom : Atom) (hError : atom.isError = false) :
    ((atom == emptyA || atom.isError) && atom != atom) = false := by
  cases hEmpty : (atom == emptyA) with
  | false => simp [hError]
  | true =>
      have hatom : atom = emptyA := (beq_empty_eq_true_iff atom).mp hEmpty
      subst atom
      rfl

/-- On a self-aligned argument, the `Empty` part of the early-stop guard is
observationally redundant: `Empty` compares equal to itself.  This is the
unconditional simplification boundary used by concrete evaluator readouts;
it avoids both a global `LawfulBEq Atom` assumption and a separate proof for
every encoded argument row. -/
theorem changedArgumentStop_self_eq_error_guard (atom : Atom) :
    ((atom == emptyA || atom.isError) && atom != atom) =
      (atom.isError && atom != atom) := by
  cases hEmpty : (atom == emptyA) with
  | false => simp
  | true =>
      have hatom : atom = emptyA := (beq_empty_eq_true_iff atom).mp hEmpty
      subst atom
      rfl

/-- A self-aligned row may test only the error part of the early-stop guard.
The `Empty` disjunct cannot contribute a changed pair, and this equality keeps
that fact available before simplification expands a concrete `zip`. -/
theorem find_changedArgumentStop_zip_self_eq_find_error_guard
    (xs : List Atom) :
    (xs.zip xs).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) =
      (xs.zip xs).find? (fun pair => pair.1.isError && pair.1 != pair.2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.zip_cons_cons, List.find?_cons,
        changedArgumentStop_self_eq_error_guard, ih]

/-- Re-evaluating a row without error atoms cannot introduce an early stop when
each result is aligned with itself.  This does not assume reflexivity of
`Atom`'s executable equality: non-`Empty` atoms short-circuit before equality,
while comparison with `Empty` is lawful by `beq_empty_eq_true_iff`. -/
theorem firstChangedArgumentStop_self_eq_none_of_forall_not_error
    (xs : List Atom)
    (h : ∀ x ∈ xs, x.isError = false) :
    firstChangedArgumentStop xs xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hxError : x.isError = false := h x (by simp)
      have htail : ∀ y ∈ xs, y.isError = false := by
        intro y hy
        exact h y (by simp [hy])
      have hxStop : ((x == emptyA || x.isError) && x != x) = false :=
        changedArgumentStop_self_eq_false_of_not_error x hxError
      unfold firstChangedArgumentStop at ih ⊢
      simp only [List.zip_cons_cons, List.find?_cons]
      rw [hxStop]
      simpa using ih htail

/-- Raw `List.find?` form of
`firstChangedArgumentStop_self_eq_none_of_forall_not_error`.  Marking the
boundary form as a simplification rule lets concrete encoded argument rows
discharge only their `isError = false` facts, without unfolding the stop guard
or proving executable equality reflexive. -/
@[simp] theorem find_changedArgumentStop_zip_self_eq_none_of_forall_not_error
    (xs : List Atom)
    (h : ∀ x ∈ xs, x.isError = false) :
    (xs.zip xs).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) =
      none := by
  simpa [firstChangedArgumentStop] using
    firstChangedArgumentStop_self_eq_none_of_forall_not_error xs h

/-- A pair occurring in a row with no changed terminal result cannot itself
be a changed terminal result. -/
theorem argument_not_changed_terminal_of_mem_zip
    {evaluated source : List Atom} {result original : Atom}
    (hNoError :
      ((evaluated.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hMem : (result, original) ∈ evaluated.zip source) :
    ¬ (((result == emptyA) = true ∨ result.isError = true) ∧ (result != original) = true) := by
  intro changedTerminal
  apply List.find?_eq_none.mp hNoError (result, original) hMem
  simpa only [Bool.and_eq_true, Bool.or_eq_true] using changedTerminal

/-- An all-quoted argument suffix extends one clean partial row in source
order, without evaluating an atom or changing the state.  Cleanliness is
required only for the completed row; every intermediate prefix inherits it. -/
theorem selectedArgumentFold_all_quoted_from_prefix
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st : St) (source prefixRow remaining : List Atom)
    (hNoError :
      (((prefixRow ++ remaining).zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    (remaining.zip (List.replicate remaining.length false)).foldl
        (selectedArgumentFoldStep evalRecursive
          (source.flatMap Atom.vars) source)
        ([(prefixRow, [])], st) =
      ([(prefixRow ++ remaining, [])], st) := by
  induction remaining generalizing prefixRow with
  | nil => simp
  | cons atom rest ih =>
      have hPrefix :
          ((prefixRow.zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none :=
        changedArgumentStop_prefix_none prefixRow (atom :: rest) source hNoError
      have hTailNoError :
          ((((prefixRow ++ [atom]) ++ rest).zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none := by
        simpa [List.append_assoc] using hNoError
      have hStep :
          selectedArgumentFoldStep evalRecursive
              (source.flatMap Atom.vars) source
              ([(prefixRow, [])], st) (atom, false) =
            ([(prefixRow ++ [atom], [])], st) := by
        simp [selectedArgumentFoldStep, hPrefix, Metta.instantiate_nil]
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.foldl_cons]
      rw [hStep]
      simpa [List.append_assoc] using ih (prefixRow ++ [atom]) hTailNoError

/-- Live-binding form of `selectedArgumentFold_all_quoted_from_prefix`.
Quoted arguments are not recursively evaluated, but they are instantiated by
the live row binding and that binding remains attached to the completed row. -/
theorem selectedArgumentFold_all_quoted_from_prefix_with_bindings
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st : St) (queryVars : List String)
    (source prefixRow remaining : List Atom) (bindings : Bindings)
    (hNoError :
      (((prefixRow ++ remaining.map (instantiate bindings)).zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    (remaining.zip (List.replicate remaining.length false)).foldl
        (selectedArgumentFoldStep evalRecursive queryVars source)
        ([(prefixRow, bindings)], st) =
      ([(prefixRow ++ remaining.map (instantiate bindings), bindings)], st) := by
  induction remaining generalizing prefixRow with
  | nil => simp
  | cons atom rest ih =>
      have hPrefix :
          ((prefixRow.zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none :=
        changedArgumentStop_prefix_none prefixRow
          ((instantiate bindings atom) :: rest.map (instantiate bindings))
          source (by simpa using hNoError)
      have hTailNoError :
          ((((prefixRow ++ [instantiate bindings atom]) ++
                rest.map (instantiate bindings)).zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none := by
        simpa [List.append_assoc] using hNoError
      have hStep :
          selectedArgumentFoldStep evalRecursive queryVars source
              ([(prefixRow, bindings)], st) (atom, false) =
            ([(prefixRow ++ [instantiate bindings atom], bindings)], st) := by
        simp [selectedArgumentFoldStep, hPrefix]
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.foldl_cons]
      rw [hStep]
      simpa [List.append_assoc] using
        ih (prefixRow ++ [instantiate bindings atom]) hTailNoError

/-- Starting from the empty partial row, a clean all-quoted application
produces exactly its source row and preserves the state. -/
theorem selectedArgumentFold_all_quoted
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st : St) (args : List Atom)
    (hNoError :
      ((args.zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    (args.zip (List.replicate args.length false)).foldl
        (selectedArgumentFoldStep evalRecursive
          (args.flatMap Atom.vars) args)
        ([([], [])], st) =
      ([(args, [])], st) := by
  simpa using
    selectedArgumentFold_all_quoted_from_prefix
      evalRecursive st args [] args hNoError

/-- Starting from a live applicability seed, a clean all-quoted application
produces the instantiated source row, retains the seed, and preserves state. -/
theorem selectedArgumentFold_all_quoted_with_bindings
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st : St) (queryVars : List String) (args : List Atom)
    (bindings : Bindings)
    (hNoError :
      (((args.map (instantiate bindings)).zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    (args.zip (List.replicate args.length false)).foldl
        (selectedArgumentFoldStep evalRecursive queryVars args)
        ([([], bindings)], st) =
      ([(args.map (instantiate bindings), bindings)], st) := by
  simpa using
    selectedArgumentFold_all_quoted_from_prefix_with_bindings
      evalRecursive st queryVars args [] args bindings hNoError

/-- With no applicability-produced seed, the expected-aware application worker
retains exactly the variables occurring in its source arguments.  Naming this
definitional boundary keeps downstream proofs independent of the worker's
nonempty-seed branch. -/
@[simp] theorem expectedApplicationRetentionScope_nil
    (args : List Atom) :
    expectedApplicationRetentionScope [] args = args.flatMap Atom.vars := rfl

/-- A closed singleton argument contributes no new public variable beyond
the variables already visible in a nonempty incoming binding. -/
theorem expectedApplicationRetentionScope_singleton_closed
    (incoming : Bindings) (atom : Atom) (hclosed : atom.vars = []) :
    expectedApplicationRetentionScope incoming [atom] = incoming.vars := by
  cases incoming <;>
    simp [expectedApplicationRetentionScope, hclosed, Bindings.vars]

/-- Append the last quoted argument to a partial argument row unless a changed
error has already stopped that row. -/
def completeQuotedTailArgument
    (source : List Atom) (templ : Atom) (part : List Atom × Bindings) :
    List Atom × Bindings :=
  match
      (part.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | some _ => part
  | none => (part.1 ++ [instantiate part.2 templ], part.2)

/-- Completing a quoted tail cannot invalidate an arbitrary state invariant.
If an earlier quoted argument already changed into an error, the outer fold
keeps the accumulator state.  Otherwise completion is exactly the appended
row covered by `happend`. -/
theorem mettaEvalExprPartFoldStep_completeQuotedTail_preserves_state_pred
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (source : List Atom) (bnd : Bindings) (returnAtom : Bool)
    (templ : Atom) (part : List Atom × Bindings)
    (acc : List (Atom × Bindings) × St) (P : St → Prop)
    (hacc : P acc.2)
    (happend :
      P (mettaEvalExprPartFoldStep env fuel queryVars op source bnd returnAtom
        acc (part.1 ++ [instantiate part.2 templ], part.2)).2) :
    P (mettaEvalExprPartFoldStep env fuel queryVars op source bnd returnAtom
      acc (completeQuotedTailArgument source templ part)).2 := by
  cases hChanged :
      (part.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | some changed =>
      simpa [completeQuotedTailArgument, hChanged,
        mettaEvalExprPartFoldStep] using hacc
  | none =>
      simpa [completeQuotedTailArgument, hChanged] using happend

/-- If the completed row itself contains no changed argument error, completion
must have taken the append branch.  A stopped row would preserve the changed
error that stopped it, contradicting the clean completed scan. -/
theorem completeQuotedTailArgument_eq_append_of_completed_clean
    (source : List Atom) (templ : Atom) (part : List Atom × Bindings)
    (hClean :
      ((completeQuotedTailArgument source templ part).1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) = none) :
    completeQuotedTailArgument source templ part =
      (part.1 ++ [instantiate part.2 templ], part.2) := by
  cases hChanged :
      (part.1.zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | none => simp [completeQuotedTailArgument, hChanged]
  | some changed =>
      simp [completeQuotedTailArgument, hChanged] at hClean

/-- Completing quoted tails is an ordered map and leaves the threaded state
unchanged. -/
theorem foldl_completeQuotedTailArgument
    (source : List Atom) (templ : Atom) (st : St)
    (pref rows : List (List Atom × Bindings)) :
    List.foldl
        (fun acc part =>
          match
              (part.1.zip source).find?
                (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
          | some _ => (acc.1 ++ [part], acc.2)
          | none =>
              (acc.1 ++ [(part.1 ++ [instantiate part.2 templ], part.2)],
                acc.2))
        (pref, st) rows =
      (pref ++ rows.map (completeQuotedTailArgument source templ), st) := by
  induction rows generalizing pref with
  | nil => simp
  | cons row tail ih =>
      rw [List.foldl_cons]
      cases hChanged :
          (row.1.zip source).find?
            (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
      | none =>
          simpa [completeQuotedTailArgument, hChanged, List.append_assoc] using
            ih (pref ++ [(row.1 ++ [instantiate row.2 templ], row.2)])
      | some changed =>
          simpa [completeQuotedTailArgument, hChanged, List.append_assoc] using
            ih (pref ++ [row])

/-- A clean completed row produced by the quoted/evaluated/quoted argument
worker has a genuine middle-argument evaluation witness.  The statement is
membership-shaped rather than a whole-list equality because an earlier quoted
atom can itself be a changed error when host equality is non-reflexive. -/
theorem quotedEvalQuoted_argumentPartials_middle_mem
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st stArg : St) (p atom templ out : Atom)
    (argPairs : List (Atom × Bindings)) (partBnd : Bindings)
    (hArg : evalRecursive st [] atom = (argPairs, stArg))
    (hmem :
      ([p, out, templ], partBnd) ∈
        (([p, atom, templ].zip [false, true, false]).foldl
          (selectedArgumentFoldStep evalRecursive
            ([p, atom, templ].flatMap Atom.vars) [p, atom, templ])
          ([([], [])], st)).1) :
    ∃ outBnd, (out, outBnd) ∈ argPairs := by
  simp only [List.zip_cons_cons, List.zip_nil_left, List.foldl_cons,
    List.foldl_nil] at hmem
  unfold selectedArgumentFoldStep at hmem
  have hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) := by
    intro hChanged
    simp [Metta.instantiate_nil, hChanged] at hmem
  simp [hPNotChanged, Metta.instantiate_nil] at hmem
  rw [hArg] at hmem
  let rows : List (List Atom × Bindings) :=
    argPairs.map fun result =>
      ([p, result.1],
        restrictBnd (p.vars ++ (atom.vars ++ templ.vars))
          ((Bindings.merge [] result.2).head?.getD result.2))
  have hfold :
      List.foldl
          (fun acc part =>
            match
                (part.1.zip [p, atom, templ]).find?
                  (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
            | some _ => (acc.1 ++ [part], acc.2)
            | none =>
                (acc.1 ++ [(part.1 ++ [instantiate part.2 templ], part.2)],
                  acc.2))
          ([], stArg) rows =
        (rows.map (completeQuotedTailArgument [p, atom, templ] templ), stArg) := by
    simpa using
      foldl_completeQuotedTailArgument [p, atom, templ] templ stArg [] rows
  change ([p, out, templ], partBnd) ∈
      (List.foldl
        (fun acc part =>
          match
              (part.1.zip [p, atom, templ]).find?
                (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
          | some _ => (acc.1 ++ [part], acc.2)
          | none =>
              (acc.1 ++ [(part.1 ++ [instantiate part.2 templ], part.2)],
                acc.2))
        ([], stArg) rows).1 at hmem
  rw [hfold] at hmem
  rcases List.mem_map.mp hmem with ⟨row, hrow, hcomplete⟩
  rcases List.mem_map.mp hrow with ⟨result, hresult, rfl⟩
  cases hChanged :
      List.find? (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)
        [(p, p), (result.1, atom)] with
  | none =>
      have hout := congrArg (fun completed => completed.1.tail.head?) hcomplete
      have : result.1 = out := by
        simpa [completeQuotedTailArgument, hChanged] using hout
      rcases result with ⟨resultAtom, resultBnd⟩
      dsimp at this
      subst resultAtom
      exact ⟨resultBnd, hresult⟩
  | some changed =>
      have hlength := congrArg (fun completed => completed.1.length) hcomplete
      simp [completeQuotedTailArgument, hChanged] at hlength

private theorem expectedArgumentFold_eq_selectedArgumentFold
    (evalExpected : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (evalOrdinary : St → Bindings → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom)
    (policies : List (Atom × (Bool × Atom)))
    (initial : List (List Atom × Bindings) × St)
    (hneutral : ∀ ae ∈ policies, ae.2.1 = true →
      ae.2.2 = Atom.sym "%Undefined%")
    (heval : ∀ st bnd atom,
      evalExpected st bnd atom (Atom.sym "%Undefined%") =
        evalOrdinary st bnd atom) :
    policies.foldl (expectedArgumentFoldStep evalExpected queryVars source) initial =
      (policies.map fun ae => (ae.1, ae.2.1)).foldl
        (selectedArgumentFoldStep evalOrdinary queryVars source) initial := by
  induction policies generalizing initial with
  | nil => rfl
  | cons ae policies ih =>
      have htail : ∀ x ∈ policies, x.2.1 = true →
          x.2.2 = Atom.sym "%Undefined%" := by
        intro x hx
        exact hneutral x (by simp [hx])
      rw [List.foldl_cons, List.map_cons, List.foldl_cons]
      have hhead :
          expectedArgumentFoldStep evalExpected queryVars source initial ae =
            selectedArgumentFoldStep evalOrdinary queryVars source initial
              (ae.1, ae.2.1) := by
        unfold expectedArgumentFoldStep selectedArgumentFoldStep
        split
        · have hae : ae.2.2 = Atom.sym "%Undefined%" :=
            hneutral ae (by simp) (by assumption)
          rw [hae]
          congr 1
          funext
          simp [heval]
        · rfl
      rw [hhead]
      exact ih _ htail

private theorem zip_argumentPolicies_map_fst {α β γ : Type}
    (xs : List α) (ys : List (β × γ)) :
    (xs.zip ys).map (fun pair => (pair.1, pair.2.1)) =
      xs.zip (ys.map Prod.fst) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [ih]

private theorem mem_of_mem_zip_right {α β : Type} {x : α} {y : β}
    {xs : List α} {ys : List β} (h : (x, y) ∈ xs.zip ys) : y ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x' xs ih =>
      cases ys with
      | nil => simp at h
      | cons y' ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact Or.inl (Prod.mk.inj h).2
          · exact Or.inr (ih h)

private def expectedResultFoldStep
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (acc : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) :
    List (Atom × Bindings) × St :=
  match (part.1.zip args).find?
      (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | some (error, _) => (acc.1 ++ [(error, part.2)], acc.2)
  | none =>
      let application := Atom.expr (Atom.sym op :: part.1)
      let (pairs, st') := reduceApplication acc.2 application
      let (out, st'') := pairs.foldl
        (fun (inner : List (Atom × Bindings) × St) result =>
          let retained := restrictBnd queryVars
            ((Bindings.merge part.2 result.2).head?.getD result.2)
          if result.1 == notReducibleA || result.1 == application then
            (inner.1 ++ [(application, part.2)], inner.2)
          else if returnsAtom selected then
            (inner.1 ++ [(result.1, retained)], inner.2)
          else
            let (more, st3) := evalRecursive inner.2 retained result.1
              (selectedResultExpected selected)
            (inner.1 ++ more.map (fun next =>
              (next.1, restrictBnd queryVars
                ((Bindings.merge retained next.2).head?.getD next.2))), st3))
        ([], st')
      (acc.1 ++ out, st'')

def selectedResultFoldStep
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (op : String) (args : List Atom)
    (returnAtom : Bool)
    (acc : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) :
    List (Atom × Bindings) × St :=
  match (part.1.zip args).find?
      (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
  | some (error, _) => (acc.1 ++ [(error, part.2)], acc.2)
  | none =>
      let application := Atom.expr (Atom.sym op :: part.1)
      let (pairs, st') := reduceApplication acc.2 application
      let (out, st'') := pairs.foldl
        (fun (inner : List (Atom × Bindings) × St) result =>
          let retained := restrictBnd queryVars
            ((Bindings.merge part.2 result.2).head?.getD result.2)
          if result.1 == notReducibleA || result.1 == application then
            (inner.1 ++ [(application, part.2)], inner.2)
          else if returnAtom then
            (inner.1 ++ [(result.1, retained)], inner.2)
          else
            let (more, st3) := evalRecursive inner.2 retained result.1
            (inner.1 ++ more.map (fun next =>
              (next.1, restrictBnd queryVars
                ((Bindings.merge retained next.2).head?.getD next.2))), st3))
        ([], st')
      (acc.1 ++ out, st'')

theorem expectedResultFoldStep_eq_selectedResultFoldStep
    (evalExpected : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (evalOrdinary : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (hresult : returnsAtom selected = false →
      selectedResultExpected selected = Atom.sym "%Undefined%")
    (heval : ∀ st bnd atom,
      evalExpected st bnd atom (Atom.sym "%Undefined%") =
        evalOrdinary st bnd atom) :
    expectedResultFoldStep evalExpected reduceApplication queryVars op args selected =
      selectedResultFoldStep evalOrdinary reduceApplication queryVars op args
        (returnsAtom selected) := by
  funext acc part
  cases hret : returnsAtom selected with
  | false =>
      have hexpected := hresult hret
      simp [expectedResultFoldStep, selectedResultFoldStep, hret, hexpected, heval]
  | true =>
      simp [expectedResultFoldStep, selectedResultFoldStep, hret]

/-- The complete argument phase of the live-seed expected application worker.
This name is the public proof boundary for consumers that compute a concrete
argument row: it retains the incoming seed, expected types, result bindings,
and left-to-right state chronology exactly as the executable does. -/
def expectedApplicationArgumentFold
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st : St) (args : List Atom)
    (selected : SelectedFunctionType) :
    List (List Atom × Bindings) × St :=
  let queryVars := expectedApplicationRetentionScope initialBindings args
  let policies := argumentEvaluationPolicies selected args.length
  (args.zip policies).foldl
    (expectedArgumentFoldStep evalRecursive queryVars args)
      ([([], initialBindings)], st)

/-- Exact live argument phase for one recursively evaluated argument.

The recursive readout and the public merge/projection are supplied as equations.  This is the
public boundary for concrete unary consumers; they do not need to unfold the private fold step. -/
theorem expectedApplicationArgumentFold_unary_eq
    (evalExpected : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stOut : St)
    (arg out expected : Atom) (resultBindings partBindings : Bindings)
    (selected : SelectedFunctionType)
    (hPolicy : argumentEvaluationPolicies selected 1 = [(true, expected)])
    (hEval : evalExpected st initialBindings arg expected =
      ([(out, resultBindings)], stOut))
    (hProject :
      restrictBnd
          (expectedApplicationRetentionScope initialBindings [arg])
          ((Bindings.merge initialBindings resultBindings).head?.getD resultBindings) =
        partBindings) :
  expectedApplicationArgumentFold evalExpected initialBindings st [arg] selected =
      ([([out], partBindings)], stOut) := by
  unfold expectedApplicationArgumentFold
  simp only [List.length_cons, List.length_nil]
  rw [hPolicy]
  simp [expectedArgumentFoldStep, hEval, hProject]

/-- The live argument phase for an all-quoted policy.  Every source argument
is instantiated by the incoming theory, no recursive evaluator call occurs,
and the same incoming theory remains attached to the completed row. -/
theorem expectedApplicationArgumentFold_all_quoted
    (evalExpected : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st : St) (args : List Atom)
    (selected : SelectedFunctionType)
    (hMask : argMask selected args.length =
      List.replicate args.length false)
    (hNoError :
      (((args.map (instantiate initialBindings)).zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    expectedApplicationArgumentFold evalExpected initialBindings st args selected =
      ([(args.map (instantiate initialBindings), initialBindings)], st) := by
  unfold expectedApplicationArgumentFold
  let policies :=
    args.zip (argumentEvaluationPolicies selected args.length)
  have hNeutral : ∀ ae ∈ policies, ae.2.1 = true →
      ae.2.2 = Atom.sym "%Undefined%" := by
    intro ae hae hTrue
    have hRight := mem_of_mem_zip_right hae
    have hFst : ae.2.1 ∈
        (argumentEvaluationPolicies selected args.length).map Prod.fst :=
      List.mem_map_of_mem hRight
    rw [argumentEvaluationPolicies_map_fst, hMask] at hFst
    have hFalse : ae.2.1 = false := (List.mem_replicate.mp hFst).2
    simp [hFalse] at hTrue
  have hFold := expectedArgumentFold_eq_selectedArgumentFold
    evalExpected
      (fun nextSt nextBindings nextAtom =>
        evalExpected nextSt nextBindings nextAtom (Atom.sym "%Undefined%"))
    (expectedApplicationRetentionScope initialBindings args) args policies
    ([([], initialBindings)], st) hNeutral (by intros; rfl)
  rw [hFold]
  rw [zip_argumentPolicies_map_fst]
  rw [argumentEvaluationPolicies_map_fst, hMask]
  exact selectedArgumentFold_all_quoted_with_bindings
    (fun nextSt nextBindings nextAtom =>
      evalExpected nextSt nextBindings nextAtom (Atom.sym "%Undefined%"))
    st (expectedApplicationRetentionScope initialBindings args) args
    initialBindings hNoError

/-- Exact live argument phase for a lazy ternary policy.  The condition is
evaluated under the applicability-produced incoming theory; its result theory
is merged and projected once, and that same projected theory instantiates both
quoted branches.  Every binding and state equation is supplied explicitly, so
the theorem asserts neither empty-seed coincidence nor ambient irrelevance. -/
theorem expectedApplicationArgumentFold_eval_quoted_quoted
    (evalExpected : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stCond : St)
    (cond thenAtom elseAtom condOut thenOut elseOut : Atom)
    (condBindings partBindings : Bindings)
    (selected : SelectedFunctionType)
    (hPolicies :
      argumentEvaluationPolicies selected 3 =
        [(true, .sym "Bool"), (false, .sym "Atom"),
          (false, .sym "Atom")])
    (hCond :
      evalExpected st initialBindings cond (.sym "Bool") =
        ([(condOut, condBindings)], stCond))
    (hMerge :
      restrictBnd
          (expectedApplicationRetentionScope initialBindings
            [cond, thenAtom, elseAtom])
          ((Bindings.merge initialBindings condBindings).head?.getD
            condBindings) =
        partBindings)
    (hThen : instantiate partBindings thenAtom = thenOut)
    (hElse : instantiate partBindings elseAtom = elseOut)
    (hNoError :
      (([condOut, thenOut, elseOut].zip [cond, thenAtom, elseAtom]).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    expectedApplicationArgumentFold evalExpected initialBindings st
        [cond, thenAtom, elseAtom] selected =
      ([([condOut, thenOut, elseOut], partBindings)], stCond) := by
  have hCondNotChanged :
      ¬ (((condOut == emptyA) = true ∨ condOut.isError = true) ∧
        (condOut != cond) = true) :=
    argument_not_changed_terminal_of_mem_zip hNoError (by simp)
  have hThenNotChanged :
      ¬ (((thenOut == emptyA) = true ∨ thenOut.isError = true) ∧
        (thenOut != thenAtom) = true) :=
    argument_not_changed_terminal_of_mem_zip hNoError (by simp)
  unfold expectedApplicationArgumentFold
  simp only [List.length_cons, List.length_nil]
  rw [hPolicies]
  simp only [List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  unfold expectedArgumentFoldStep
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hCond]
  simp [hMerge, hThen, hElse, hCondNotChanged, hThenNotChanged]

/-- Exact live argument phase for two recursively evaluated arguments.

The second recursive call starts from the first result's projected theory, so
the theorem records both merge/projection equations and the left-to-right state
transition explicitly.  This is the binary counterpart of
`expectedApplicationArgumentFold_unary_eq`; it makes no empty-seed or
binding-neutrality assumption. -/
theorem expectedApplicationArgumentFold_eval_eval
    (evalExpected : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stFirst stSecond : St)
    (first second firstOut secondOut firstExpected secondExpected : Atom)
    (firstResultBindings firstPartBindings secondResultBindings
      secondPartBindings : Bindings)
    (selected : SelectedFunctionType)
    (hPolicies :
      argumentEvaluationPolicies selected 2 =
        [(true, firstExpected), (true, secondExpected)])
    (hFirst :
      evalExpected st initialBindings first firstExpected =
        ([(firstOut, firstResultBindings)], stFirst))
    (hFirstMerge :
      restrictBnd
          (expectedApplicationRetentionScope initialBindings [first, second])
          ((Bindings.merge initialBindings firstResultBindings).head?.getD
            firstResultBindings) =
        firstPartBindings)
    (hSecond :
      evalExpected stFirst firstPartBindings second secondExpected =
        ([(secondOut, secondResultBindings)], stSecond))
    (hSecondMerge :
      restrictBnd
          (expectedApplicationRetentionScope initialBindings [first, second])
          ((Bindings.merge firstPartBindings secondResultBindings).head?.getD
            secondResultBindings) =
        secondPartBindings)
    (hNoError :
      (([firstOut, secondOut].zip [first, second]).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    expectedApplicationArgumentFold evalExpected initialBindings st
        [first, second] selected =
      ([([firstOut, secondOut], secondPartBindings)], stSecond) := by
  have hFirstNotChanged :
      ¬ (((firstOut == emptyA) = true ∨ firstOut.isError = true) ∧
        (firstOut != first) = true) :=
    argument_not_changed_terminal_of_mem_zip hNoError (by simp)
  unfold expectedApplicationArgumentFold
  simp only [List.length_cons, List.length_nil]
  rw [hPolicies]
  simp only [List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  unfold expectedArgumentFoldStep
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hFirst]
  simp [hFirstMerge, hFirstNotChanged]
  rw [hSecond]
  simp [hSecondMerge]

/-- The complete result phase of the live-seed expected application worker.
It consumes argument rows without changing their order or reconstructing any
of the bindings accumulated by the argument phase. -/
def expectedApplicationResultFold
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (partialsState : List (List Atom × Bindings) × St) :
    List (Atom × Bindings) × St :=
  let queryVars := expectedApplicationRetentionScope initialBindings args
  partialsState.1.foldl
    (expectedResultFoldStep evalRecursive reduceApplication queryVars op args selected)
    ([], partialsState.2)

/-- Factored presentation of the live-seed expected application worker.  The
argument fold starts from the applicability-produced binding, and the result
fold retains exactly the resulting live scope.  This is the proof boundary for
nonempty callers; the legacy selected worker is only the empty-seed special
case. -/
def evaluateExpectedApplicationFromFactored
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings)
    (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType) : List (Atom × Bindings) × St :=
  expectedApplicationResultFold evalRecursive reduceApplication initialBindings
    op args selected
    (expectedApplicationArgumentFold evalRecursive initialBindings st args selected)

/-- A left-to-right state fold preserves every predicate preserved by its
step.  This is the chronology algebra used by the expected-application
worker; alternatives are never assigned independent copies of the initial
state. -/
theorem foldl_snd_preserves_state_pred
    {Input Output State : Type}
    (step : (List Output × State) → Input → List Output × State)
    (P : State → Prop)
    (hStep : ∀ acc input, P acc.2 → P (step acc input).2)
    (inputs : List Input) (initial : List Output × State)
    (hInitial : P initial.2) :
    P (inputs.foldl step initial).2 := by
  induction inputs generalizing initial with
  | nil => simpa using hInitial
  | cons input inputs ih =>
      simp only [List.foldl_cons]
      exact ih (step initial input) (hStep initial input hInitial)

private theorem expectedArgumentFoldStep_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (queryVars : List String) (source : List Atom)
    (P : St → Prop)
    (hEval : ∀ st bindings atom expected,
      P st → P (evalRecursive st bindings atom expected).2)
    (acc : List (List Atom × Bindings) × St)
    (ae : Atom × (Bool × Atom))
    (hAcc : P acc.2) :
    P (expectedArgumentFoldStep evalRecursive queryVars source acc ae).2 := by
  unfold expectedArgumentFoldStep
  refine foldl_snd_preserves_state_pred
    (fun (acc2 : List (List Atom × Bindings) × St) part =>
      match (part.1.zip source).find?
          (fun pair =>
            (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
      | some _ => (acc2.1 ++ [part], acc2.2)
      | none =>
          if ae.2.1 then
            let (results, st') :=
              evalRecursive acc2.2 part.2 ae.1 ae.2.2
            (acc2.1 ++ results.map (fun result =>
              (part.1 ++ [result.1], restrictBnd queryVars
                ((Bindings.merge part.2 result.2).head?.getD result.2))), st')
          else
            (acc2.1 ++
              [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2))
    P ?_ acc.1 ([], acc.2) hAcc
  · intro acc2 part hP
    split
    · exact hP
    · split
      · simpa using hEval acc2.2 part.2 ae.1 ae.2.2 hP
      · exact hP

private theorem expectedApplicationArgumentFold_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st : St) (args : List Atom)
    (selected : SelectedFunctionType) (P : St → Prop)
    (hEval : ∀ nextSt bindings atom expected,
      P nextSt → P (evalRecursive nextSt bindings atom expected).2)
    (hInitial : P st) :
    P (expectedApplicationArgumentFold evalRecursive initialBindings st args
      selected).2 := by
  unfold expectedApplicationArgumentFold
  apply foldl_snd_preserves_state_pred
    (expectedArgumentFoldStep evalRecursive
      (expectedApplicationRetentionScope initialBindings args) args) P
  · intro acc ae hP
    exact expectedArgumentFoldStep_preserves_state_pred
      evalRecursive
      (expectedApplicationRetentionScope initialBindings args) args P hEval
      acc ae hP
  · exact hInitial

private theorem expectedResultFoldStep_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (queryVars : List String) (op : String) (args : List Atom)
    (selected : SelectedFunctionType) (P : St → Prop)
    (hEval : ∀ st bindings atom expected,
      P st → P (evalRecursive st bindings atom expected).2)
    (hReduce : ∀ st application,
      P st → P (reduceApplication st application).2)
    (acc : List (Atom × Bindings) × St)
    (part : List Atom × Bindings) (hAcc : P acc.2) :
    P (expectedResultFoldStep evalRecursive reduceApplication queryVars op
      args selected acc part).2 := by
  unfold expectedResultFoldStep
  split
  · exact hAcc
  · rename_i hNoChanged
    let application := Atom.expr (Atom.sym op :: part.1)
    cases hReduceEq : reduceApplication acc.2 application with
    | mk pairs st' =>
        have hSt' : P st' := by
          have := hReduce acc.2 application hAcc
          simpa [hReduceEq] using this
        have hFold : P (pairs.foldl
          (fun (inner : List (Atom × Bindings) × St)
            (result : Atom × Bindings) =>
            let retained := restrictBnd queryVars
              ((Bindings.merge part.2 result.2).head?.getD result.2)
            if result.1 == notReducibleA || result.1 == application then
              (inner.1 ++ [(application, part.2)], inner.2)
            else if returnsAtom selected then
              (inner.1 ++ [(result.1, retained)], inner.2)
            else
              let (more, st3) := evalRecursive inner.2 retained result.1
                (selectedResultExpected selected)
              (inner.1 ++ more.map (fun next =>
                (next.1, restrictBnd queryVars
                  ((Bindings.merge retained next.2).head?.getD next.2))), st3))
          ([], st')).2 := by
          refine foldl_snd_preserves_state_pred
            (fun (inner : List (Atom × Bindings) × St)
              (result : Atom × Bindings) =>
              let retained := restrictBnd queryVars
                ((Bindings.merge part.2 result.2).head?.getD result.2)
              if result.1 == notReducibleA || result.1 == application then
                (inner.1 ++ [(application, part.2)], inner.2)
              else if returnsAtom selected then
                (inner.1 ++ [(result.1, retained)], inner.2)
              else
                let (more, st3) := evalRecursive inner.2 retained result.1
                  (selectedResultExpected selected)
                (inner.1 ++ more.map (fun next =>
                  (next.1, restrictBnd queryVars
                    ((Bindings.merge retained next.2).head?.getD next.2))), st3))
            P ?_ pairs ([], st') hSt'
          intro inner result hInner
          split
          · exact hInner
          · split
            · exact hInner
            · simpa using hEval inner.2
                (restrictBnd queryVars
                  ((Bindings.merge part.2 result.2).head?.getD result.2))
                result.1 (selectedResultExpected selected) hInner
        simpa [application, hReduceEq] using hFold

private theorem expectedApplicationResultFold_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (partialsState : List (List Atom × Bindings) × St)
    (P : St → Prop)
    (hEval : ∀ st bindings atom expected,
      P st → P (evalRecursive st bindings atom expected).2)
    (hReduce : ∀ st application,
      P st → P (reduceApplication st application).2)
    (hInitial : P partialsState.2) :
    P (expectedApplicationResultFold evalRecursive reduceApplication
      initialBindings op args selected partialsState).2 := by
  unfold expectedApplicationResultFold
  apply foldl_snd_preserves_state_pred
    (expectedResultFoldStep evalRecursive reduceApplication
      (expectedApplicationRetentionScope initialBindings args) op args selected)
    P
  · intro acc part hP
    exact expectedResultFoldStep_preserves_state_pred
      evalRecursive reduceApplication
      (expectedApplicationRetentionScope initialBindings args) op args selected
      P hEval hReduce acc part hP
  · exact hInitial

/-- The complete live selected-application worker preserves every state
predicate preserved by recursive argument/result evaluation and by root
reduction.  The theorem is seed- and policy-parametric, so DIndG consumers do
not need a per-operator reconstruction of the two ordered folds. -/
theorem evaluateExpectedApplicationFrom_preserves_state_pred
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st : St)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (P : St → Prop)
    (hEval : ∀ nextSt bindings atom expected,
      P nextSt → P (evalRecursive nextSt bindings atom expected).2)
    (hReduce : ∀ nextSt application,
      P nextSt → P (reduceApplication nextSt application).2)
    (hInitial : P st) :
    P (evaluateExpectedApplicationFrom evalRecursive reduceApplication
      initialBindings st op args selected).2 := by
  change P (expectedApplicationResultFold evalRecursive reduceApplication
    initialBindings op args selected
    (expectedApplicationArgumentFold evalRecursive initialBindings st args
      selected)).2
  apply expectedApplicationResultFold_preserves_state_pred
    evalRecursive reduceApplication initialBindings op args selected
    (expectedApplicationArgumentFold evalRecursive initialBindings st args
      selected) P hEval hReduce
  exact expectedApplicationArgumentFold_preserves_state_pred
    evalRecursive initialBindings st args selected P hEval hInitial

/-- Once a concrete caller has computed the live argument phase, the complete
application is exactly the result fold over those rows.  In particular, this
theorem assumes no coincidence between evaluation under `initialBindings` and
evaluation under the empty binding. -/
theorem evaluateExpectedApplicationFromFactored_eq_resultFold_of_argumentFold
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stArgs : St)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (partials : List (List Atom × Bindings))
    (hArgs :
      expectedApplicationArgumentFold evalRecursive initialBindings st args selected =
        (partials, stArgs)) :
    evaluateExpectedApplicationFromFactored evalRecursive reduceApplication
        initialBindings st op args selected =
      expectedApplicationResultFold evalRecursive reduceApplication
        initialBindings op args selected (partials, stArgs) := by
  rw [evaluateExpectedApplicationFromFactored, hArgs]

/-- Recursion-neutral selected results may reuse the ordinary result-fold
library after the live argument phase has been computed.  The argument phase
itself remains expected-aware and binding-threaded; only result recursion at
`%Undefined%` is identified with ordinary evaluation. -/
theorem evaluateExpectedApplicationFromFactored_eq_selectedResultFold_of_argumentFold
    (evalExpected : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (evalOrdinary : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stArgs : St)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (partials : List (List Atom × Bindings))
    (hArgs :
      expectedApplicationArgumentFold evalExpected initialBindings st args selected =
        (partials, stArgs))
    (hResult : returnsAtom selected = false →
      selectedResultExpected selected = Atom.sym "%Undefined%")
    (hEval : ∀ nextSt nextBindings nextAtom,
      evalExpected nextSt nextBindings nextAtom (Atom.sym "%Undefined%") =
        evalOrdinary nextSt nextBindings nextAtom) :
    evaluateExpectedApplicationFromFactored evalExpected reduceApplication
        initialBindings st op args selected =
      partials.foldl
        (selectedResultFoldStep evalOrdinary reduceApplication
          (expectedApplicationRetentionScope initialBindings args)
          op args (returnsAtom selected))
        ([], stArgs) := by
  rw [evaluateExpectedApplicationFromFactored_eq_resultFold_of_argumentFold
    evalExpected reduceApplication initialBindings st stArgs op args selected
      partials hArgs]
  simp only [expectedApplicationResultFold]
  rw [expectedResultFoldStep_eq_selectedResultFoldStep
    evalExpected evalOrdinary reduceApplication
    (expectedApplicationRetentionScope initialBindings args) op args selected
    hResult hEval]

private def evaluateExpectedApplicationFactored
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType) : List (Atom × Bindings) × St :=
  evaluateExpectedApplicationFromFactored evalRecursive reduceApplication []
    st op args selected

def evaluateSelectedApplicationFactored
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool) : List (Atom × Bindings) × St :=
  let queryVars := args.flatMap Atom.vars
  let partialsState := (args.zip mask).foldl
    (selectedArgumentFoldStep evalRecursive queryVars args) ([([], [])], st)
  partialsState.1.foldl
    (selectedResultFoldStep evalRecursive reduceApplication queryVars op args returnAtom)
    ([], partialsState.2)

private theorem evaluateExpectedApplication_eq_factored :
    @evaluateExpectedApplication = @evaluateExpectedApplicationFactored := by
  rfl

/-- The executable live-seed worker is definitionally its two-fold
presentation.  Consumers should rewrite through this theorem rather than
unfold the evaluator body. -/
theorem evaluateExpectedApplicationFrom_eq_factored :
    @evaluateExpectedApplicationFrom = @evaluateExpectedApplicationFromFactored := by
  rfl

theorem evaluateSelectedApplication_eq_factored :
    @evaluateSelectedApplication = @evaluateSelectedApplicationFactored := by
  rfl

/-- A clean all-quoted application reaches the result worker with exactly one
source-ordered row and the original state.  This is the boundary consumed by
fixed-arity quoted-operator proofs; no downstream proof needs to unfold the
argument worker or replay its prefix chronology. -/
theorem evaluateSelectedApplicationFactored_all_quoted
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom) (returnAtom : Bool)
    (hNoError :
      ((args.zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    evaluateSelectedApplicationFactored evalRecursive reduceApplication st op
        args (List.replicate args.length false) returnAtom =
      selectedResultFoldStep evalRecursive reduceApplication
        (args.flatMap Atom.vars) op args returnAtom ([], st) (args, []) := by
  dsimp only [evaluateSelectedApplicationFactored]
  rw [selectedArgumentFold_all_quoted evalRecursive st args hNoError]
  rfl

/-- The factored selected-result worker is exactly the named expression-part
fold used by runtime-correctness proofs. -/
theorem selectedResultFoldStep_eq_mettaEvalExprPartFoldStep
    (env : MinEnv) (fuel : Nat) (queryVars : List String)
    (op : String) (args : List Atom) (bnd : Bindings) (returnAtom : Bool) :
    selectedResultFoldStep
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        queryVars op args returnAtom =
      mettaEvalExprPartFoldStep env fuel queryVars op args bnd returnAtom := by
  funext acc part
  unfold selectedResultFoldStep mettaEvalExprPartFoldStep
  split
  · rfl
  · have hrootEq :
        (fun inner result =>
          if (result.1 == notReducibleA) = true ∨
              (result.1 == Atom.expr (Atom.sym op :: part.1)) = true then
            (inner.1 ++ [(Atom.expr (Atom.sym op :: part.1), part.2)], inner.2)
          else if returnAtom = true then
            (inner.1 ++
                [(result.1,
                  restrictBnd queryVars
                    ((Bindings.merge part.2 result.2).head?.getD result.2))],
              inner.2)
          else
            (inner.1 ++
                (mettaEval env fuel inner.2
                  (restrictBnd queryVars
                    ((Bindings.merge part.2 result.2).head?.getD result.2))
                  result.1).1.map (fun next =>
                    (next.1,
                      restrictBnd queryVars
                        ((Bindings.merge
                          (restrictBnd queryVars
                            ((Bindings.merge part.2 result.2).head?.getD result.2))
                          next.2).head?.getD next.2))),
              (mettaEval env fuel inner.2
                (restrictBnd queryVars
                  ((Bindings.merge part.2 result.2).head?.getD result.2))
                result.1).2)) =
          mettaEvalExprRootFoldStep env fuel queryVars
            (Atom.expr (Atom.sym op :: part.1)) part.2 returnAtom := by
      funext inner result
      simp [mettaEvalExprRootFoldStep]
    simp [hrootEq]

/-- Runtime specialization of `evaluateSelectedApplicationFactored_all_quoted`:
after the clean quoted argument fold, the sole remaining step is the named
expression-part result worker. -/
theorem evaluateSelectedApplicationFactored_all_quoted_eq_mettaEvalExprPartFoldStep
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (op : String) (args : List Atom) (returnAtom : Bool)
    (hNoError :
      ((args.zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    evaluateSelectedApplicationFactored
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        st op args (List.replicate args.length false) returnAtom =
      mettaEvalExprPartFoldStep env fuel (args.flatMap Atom.vars)
        op args bnd returnAtom ([], st) (args, []) := by
  rw [evaluateSelectedApplicationFactored_all_quoted _ _ st op args returnAtom hNoError]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]

/-- Live-seed all-quoted readout.  Unlike the legacy empty-seed theorem, the
completed argument row contains the arguments instantiated by `bnd`, carries
`bnd` into reduction, and retains the full live application scope. -/
theorem evaluateExpectedApplicationFromFactored_all_quoted_eq_mettaEvalExprPartFoldStep
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (returnAtom : Bool)
    (hMask : argMask selected args.length = List.replicate args.length false)
    (hReturn : returnsAtom selected = returnAtom)
    (hResult : returnsAtom selected = false →
      selectedResultExpected selected = Atom.sym "%Undefined%")
    (hNoError :
      (((args.map (instantiate bnd)).zip args).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    evaluateExpectedApplicationFromFactored
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        bnd st op args selected =
      mettaEvalExprPartFoldStep env fuel
        (expectedApplicationRetentionScope bnd args)
        op args bnd returnAtom ([], st)
        (args.map (instantiate bnd), bnd) := by
  have hArgs := expectedApplicationArgumentFold_all_quoted
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    bnd st args selected hMask hNoError
  rw [evaluateExpectedApplicationFromFactored_eq_selectedResultFold_of_argumentFold
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    (fun nextSt nextBindings nextAtom =>
      mettaEval env fuel nextSt nextBindings nextAtom)
    (fun nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
    bnd st st op args selected
    [(args.map (instantiate bnd), bnd)] hArgs hResult
    (mettaEvalExpected_undefined env fuel)]
  rw [hReturn]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]

/-- Exact typed-result worker for one clean all-quoted row and one root.

Unlike the recursion-neutral specialization above, this theorem keeps the
selected result expectation and calls `mettaEvalExpected` on the reduced root.
It therefore covers ground typed results such as `Bool` without asserting an
expected/ordinary evaluator coincidence.  Both binding projections remain in
the conclusion because they are observable and need not reproduce the input
list syntactically. -/
theorem evaluateExpectedApplicationFromFactored_all_quoted_eq_of_root_expected_eq
    (env : MinEnv) (fuel : Nat) (st stRoot stOut : St)
    (bnd : Bindings) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (root final : Atom) (rootBnd finalBnd : Bindings)
    (hMask : argMask selected args.length = List.replicate args.length false)
    (hReturn : returnsAtom selected = false)
    (hNoError :
      (((args.map (instantiate bnd)).zip args).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval",
              Atom.expr (Atom.sym op :: args.map (instantiate bnd))]) [],
           bnd := bnd }] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf :
      (root == Atom.expr (Atom.sym op :: args.map (instantiate bnd))) = false)
    (hFinal :
      mettaEvalExpected env fuel stRoot
          (restrictBnd
            (expectedApplicationRetentionScope bnd args)
            ((Bindings.merge bnd rootBnd).head?.getD rootBnd))
          root (selectedResultExpected selected) =
        ([(final, finalBnd)], stOut)) :
    evaluateExpectedApplicationFromFactored
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        bnd st op args selected =
      ([(final,
          restrictBnd
            (expectedApplicationRetentionScope bnd args)
            ((Bindings.merge
              (restrictBnd
                (expectedApplicationRetentionScope bnd args)
                ((Bindings.merge bnd rootBnd).head?.getD rootBnd))
              finalBnd).head?.getD finalBnd))],
        stOut) := by
  have hArgs := expectedApplicationArgumentFold_all_quoted
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    bnd st args selected hMask hNoError
  rw [evaluateExpectedApplicationFromFactored_eq_resultFold_of_argumentFold
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    (fun nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
    bnd st st op args selected
    [(args.map (instantiate bnd), bnd)] hArgs]
  simp only [expectedApplicationResultFold, List.foldl_cons, List.foldl_nil]
  unfold expectedResultFoldStep
  rw [hNoError]
  simp only [List.nil_append]
  rw [hRoot]
  simp [hRootNotNotReducible, hRootNotSelf, hReturn]
  rw [hFinal]
  simp

/-- Exact worker boundary for a lazy ternary application: the condition is
evaluated under its declared expected type, both branches are quoted, and the
`%Undefined%` result policy hands the completed row to the ordinary
expression-part fold.  This theorem is intentionally policy-specific; it
does not assert a general expected/ordinary evaluator coincidence. -/
theorem evaluateExpectedApplication_eval_quoted_quoted_eq_mettaEvalExprPartFoldStep
    (env : MinEnv) (fuel : Nat) (st stCond : St) (op : String)
    (cond thenAtom elseAtom condOut : Atom)
    (policy : EvalQuotedQuotedApplicationPolicy env st.world op
      [cond, thenAtom, elseAtom] (Atom.sym "Bool"))
    (hCond :
      mettaEvalExpected env fuel st [] cond (Atom.sym "Bool") =
        ([(condOut, [])], stCond))
    (hNoError :
      (([condOut, thenAtom, elseAtom].zip [cond, thenAtom, elseAtom]).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    evaluateExpectedApplication
        (fun nextSt nextBindings nextAtom expected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom expected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := [] }] [])
        st op [cond, thenAtom, elseAtom] policy.raw.decision.selectedType =
      mettaEvalExprPartFoldStep env fuel
        ([cond, thenAtom, elseAtom].flatMap Atom.vars)
        op [cond, thenAtom, elseAtom] [] false ([], stCond)
        ([condOut, thenAtom, elseAtom], []) := by
  have hCondNotChanged :
      ¬ (((condOut == emptyA) = true ∨ condOut.isError = true) ∧ (condOut != cond) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := condOut) (original := cond) hNoError (by simp)
  have hThenNotChanged :
      ¬ (((thenAtom == emptyA) = true ∨ thenAtom.isError = true) ∧ (thenAtom != thenAtom) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := thenAtom) (original := thenAtom) hNoError (by simp)
  rw [evaluateExpectedApplication_eq_factored]
  dsimp only [evaluateExpectedApplicationFactored,
    evaluateExpectedApplicationFromFactored,
    expectedApplicationArgumentFold, expectedApplicationResultFold]
  simp only [List.length_cons, List.length_nil]
  rw [policy.argumentPolicies_eq]
  rw [expectedApplicationRetentionScope_nil]
  rw [expectedResultFoldStep_eq_selectedResultFoldStep
    (mettaEvalExpected env fuel) (mettaEval env fuel)
    (fun nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := [] }] [])
    ([cond, thenAtom, elseAtom].flatMap Atom.vars) op
    [cond, thenAtom, elseAtom] policy.raw.decision.selectedType
    (by
      intro _
      exact policy.resultExpected_eq)
    (mettaEvalExpected_undefined env fuel)]
  rw [policy.raw.returnsAtom_selectedType_eq]
  simp only [List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  unfold expectedArgumentFoldStep
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hCond]
  simp [restrictBnd_empty_merge_empty, Metta.instantiate_nil,
    hCondNotChanged, hThenNotChanged]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]

/-- The expected-aware executor reduces to the legacy mask-only executor only under explicit,
checked recursion-neutrality conditions.  This is the sole compatibility route for downstream
proofs; genuinely typed argument or result policies must reason about expected-aware recursion. -/
theorem evaluateExpectedApplication_eq_evaluateSelectedApplication_of_recursionNeutral
    (evalExpected : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (evalOrdinary : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (hneutral : SelectedApplicationRecursionNeutral selected args.length)
    (heval : ∀ st bnd atom,
      evalExpected st bnd atom (Atom.sym "%Undefined%") =
        evalOrdinary st bnd atom) :
    evaluateExpectedApplication evalExpected reduceApplication st op args selected =
      evaluateSelectedApplication evalOrdinary reduceApplication st op args
        (argMask selected args.length) (returnsAtom selected) := by
  rw [evaluateExpectedApplication_eq_factored, evaluateSelectedApplication_eq_factored]
  unfold evaluateExpectedApplicationFactored evaluateSelectedApplicationFactored
  let policies := argumentEvaluationPolicies selected args.length
  let expectedPartials :=
    (args.zip policies).foldl
      (expectedArgumentFoldStep evalExpected (args.flatMap Atom.vars) args)
        ([([], [])], st)
  let ordinaryPartials :=
    (args.zip (argMask selected args.length)).foldl
      (selectedArgumentFoldStep evalOrdinary (args.flatMap Atom.vars) args)
        ([([], [])], st)
  have harg : expectedPartials = ordinaryPartials := by
    unfold expectedPartials ordinaryPartials
    rw [expectedArgumentFold_eq_selectedArgumentFold
      evalExpected evalOrdinary (args.flatMap Atom.vars) args
      (args.zip policies) ([([], [])], st)]
    · rw [zip_argumentPolicies_map_fst, argumentEvaluationPolicies_map_fst]
    · intro ae hae htrue
      exact hneutral.argumentExpected ae.2 (mem_of_mem_zip_right hae) htrue
    · exact heval
  change expectedPartials.1.foldl
      (expectedResultFoldStep evalExpected reduceApplication (args.flatMap Atom.vars)
        op args selected) ([], expectedPartials.2) =
    ordinaryPartials.1.foldl
      (selectedResultFoldStep evalOrdinary reduceApplication (args.flatMap Atom.vars)
        op args (returnsAtom selected)) ([], ordinaryPartials.2)
  rw [harg]
  rw [expectedResultFoldStep_eq_selectedResultFoldStep
    evalExpected evalOrdinary reduceApplication (args.flatMap Atom.vars)
    op args selected hneutral.resultExpected heval]

/-- A non-error application policy exposes exactly the evaluator branch selected at runtime.

The recursive evaluator and reducer below are the literal callbacks used by `mettaEval`; this
equation is the single proof boundary shared by selected signatures and untyped tuple fallback. -/
theorem mettaEval_eq_evaluateExpectedApplication_of_selected
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hSelected : selectFunctionType env st.world (.sym op) args = .selected selected)
    (planCorresponds : ApplicationPlanCorresponds []
      (.selected selected hSelected)) :
    mettaEval env (fuel + 1) st [] (Atom.expr (Atom.sym op :: args)) =
      prioritizeSemanticResults (evaluateExpectedApplication
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := [] }] [])
        st op args selected) := by
  conv_lhs => unfold mettaEval
  rw [instantiate_nil (Atom.expr (Atom.sym op :: args))]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  have hScan :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args
          (.sym "%Undefined%") [] = .selected selected := by
    simpa [ExactApplicationPolicy.planScanOutcome] using planCorresponds.scan
  obtain ⟨headBindings, hHead, hSeed⟩ := by
    simpa [ExactApplicationPolicy.headSeedCorresponds] using
      planCorresponds.headSeed
  rw [executeApplicationPlan, hScan]
  simp only [executeSelectedApplicationPlan, hHead, hSeed]
  rfl

/-- Expected-aware evaluation exposes the complete left-to-right fold over the
public applicability seeds produced by its selected signature.  This is the
authoritative selected-branch equation; no public binding is projected away. -/
theorem mettaEvalExpected_eq_evaluateExpectedApplicationSeeds_of_selected
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (expected : Atom) (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (selected : SelectedFunctionType)
    (hSelected :
      selectFunctionTypeForExpected env st.world (.sym op) args expected =
        .selected selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world selected.typeBindings (.sym op)
      selected.functionType = .inr headBindings) :
    mettaEvalExpected env (fuel + 1) st [] (.expr (.sym op :: args)) expected =
      prioritizeSemanticResults (evaluateExpectedApplicationSeeds
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun bindings nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (.expr [.sym "eval", application]) [],
               bnd := bindings }] [])
        (selectedApplicationInitialBindingsFromTheory []
          (.expr (.sym op :: args)) expected headBindings)
        st op args selected) := by
  conv_lhs => rw [mettaEvalExpected]
  rw [hExpected]
  simp only [Bool.false_eq_true, ↓reduceIte, Metta.instantiate_nil]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Atom.metaType, Atom.typeAtomOfMetaType]
  have hExpressionNotVariable :
      (MetaType.expression == MetaType.variable) = false := rfl
  have hSelectedAvoiding :
      selectFunctionTypeForExpectedAvoiding env st.world (.sym op) args
          expected [] = .selected selected := by
    simpa [selectFunctionTypeForExpected] using hSelected
  have hSelectedFrom :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args
          expected [] = .selected selected := by
    rw [selectFunctionTypeForExpectedFrom_empty]
    exact hSelectedAvoiding
  simp [hNeedsInterpret, hExpressionNotVariable]
  rw [executeApplicationPlan, hSelectedFrom]
  simp only [executeSelectedApplicationPlan, hHead]

/-- Live-binding form of
`mettaEvalExpected_eq_evaluateExpectedApplicationSeeds_of_selected`.

Expected evaluation instantiates its source once at entry and again after the
boundary type check.  The second equation is therefore explicit: it is true
for the closed concrete applications used by the kernel, but is not assumed
for arbitrary incoming bindings.  The selected applicability theory may
produce any finite list of public seeds; no singleton or raw-selector
coincidence is built into this boundary. -/
theorem mettaEvalExpected_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom) (expected : Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hStable : instantiate bnd (Atom.expr (Atom.sym op :: args)) =
      Atom.expr (Atom.sym op :: args))
    (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (selected : SelectedFunctionType)
    (hSelected :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args expected bnd =
        .selected selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world selected.typeBindings (.sym op)
      selected.functionType = .inr headBindings) :
    mettaEvalExpected env (fuel + 1) st bnd source expected =
      prioritizeSemanticResults (evaluateExpectedApplicationSeeds
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun bindings nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (.expr [.sym "eval", application]) [],
               bnd := bindings }] [])
        (selectedApplicationInitialBindingsFromTheory bnd
          (.expr (.sym op :: args)) expected headBindings)
        st op args selected) := by
  conv_lhs => rw [mettaEvalExpected]
  rw [hExpected]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hInstantiate]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Atom.metaType, Atom.typeAtomOfMetaType]
  have hExpressionNotVariable :
      (MetaType.expression == MetaType.variable) = false := rfl
  simp only [hNeedsInterpret, hExpressionNotVariable]
  rw [hStable]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [executeApplicationPlan, hSelected]
  simp only [executeSelectedApplicationPlan, hHead]

/-- When the selected applicability theory contributes exactly the neutral
seed, the exact seed fold reduces to the ordinary single-application boundary.
The premise is intentionally explicit: repair #19 makes the corresponding
claim false for caller-visible dependent bindings. -/
theorem mettaEvalExpected_eq_evaluateExpectedApplication_of_selected
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (expected : Atom) (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (selected : SelectedFunctionType)
    (hSelected :
      selectFunctionTypeForExpected env st.world (.sym op) args expected =
        .selected selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world selected.typeBindings (.sym op)
      selected.functionType = .inr headBindings)
    (hInitial : selectedApplicationInitialBindingsFromTheory []
      (.expr (.sym op :: args)) expected headBindings = [[]]) :
    mettaEvalExpected env (fuel + 1) st [] (.expr (.sym op :: args)) expected =
      prioritizeSemanticResults (evaluateExpectedApplication
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (.expr [.sym "eval", application]) [], bnd := [] }] [])
        st op args selected) := by
  rw [mettaEvalExpected_eq_evaluateExpectedApplicationSeeds_of_selected
    env fuel st op args expected hExpected hNeedsInterpret hNotError selected hSelected
      headBindings hHead,
    hInitial]
  rfl

/-- Matching two lists of symbols threads the empty type theory unchanged.
This deliberately excludes grounded leaves: runtime `BEq` is not reflexive
for every host float, so the corresponding theorem for arbitrary closed atoms
would be false. -/
theorem matchReducedList_map_sym_self (names : List String) :
    matchReducedList [] (names.map Atom.sym) (names.map Atom.sym) = some [] := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp [matchReducedList, matchReduced, Metta.matchAtoms,
        Metta.matchAtomsWith, Metta.Bindings.merge, Metta.Bindings.hasLoop,
        Metta.Bindings.vars, ih]

/-- Live-theory form of `matchReducedList_map_sym_self`.  Matching a closed
symbolic list preserves any loop-free incoming theory. -/
theorem matchReducedList_map_sym_self_from (bindings : Bindings)
    (hloop : Bindings.hasLoop bindings = false) (names : List String) :
    matchReducedList bindings (names.map Atom.sym) (names.map Atom.sym) =
      some bindings := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp [matchReducedList, matchReduced, Metta.matchAtoms,
        Metta.matchAtomsWith, Metta.Bindings.merge, hloop, ih]

/-- Expected-selection freshening is definitionally inert on a type made only
from symbols.  This is the closed-signature boundary used by concrete kernel
operators; signatures containing variables deliberately do not satisfy it. -/
theorem freshenFunctionTypeCandidatesAvoiding_map_sym
    (env : MinEnv) (expression : Atom) (args : List Atom) (expected : Atom)
    (liveAvoid : List VarName) (names : List String) :
    freshenFunctionTypeCandidatesAvoiding env expression args expected liveAvoid
        [.expr (names.map Atom.sym)] =
      [.expr (names.map Atom.sym)] := by
  simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
    renameAllVars]

/-- Compatibility-entry form of
`freshenFunctionTypeCandidatesAvoiding_map_sym`. -/
theorem freshenFunctionTypeCandidates_map_sym
    (env : MinEnv) (expression : Atom) (args : List Atom) (expected : Atom)
    (names : List String) :
    freshenFunctionTypeCandidates env expression args expected
        [.expr (names.map Atom.sym)] =
      [.expr (names.map Atom.sym)] := by
  exact freshenFunctionTypeCandidatesAvoiding_map_sym
    env expression args expected [] names

/-- A variable-free symbolic arrow matches itself without adding type
bindings.  The single arrow-level statement keeps formal and return types in
one coherent match. -/
theorem matchType_symbolic_arrow_self (names : List String) :
    matchType [] (.expr (("->" :: names).map Atom.sym))
        (.expr (("->" :: names).map Atom.sym)) = some [] := by
  simp [matchType, matchReduced, matchReducedList,
    matchReducedList_map_sym_self, Metta.matchAtoms, Metta.matchAtomsWith,
    Metta.Bindings.merge, Metta.Bindings.hasLoop, Metta.Bindings.vars]

/-- A variable-free symbolic arrow matches itself without changing an
arbitrary live type theory.  This is the live-binding form of
`matchType_symbolic_arrow_self`; unlike the empty-theory corollary, it is
strong enough for operator-head checking after applicability has been seeded
from the caller. -/
theorem matchType_symbolic_arrow_self_from (bindings : Bindings)
    (hloop : Bindings.hasLoop bindings = false) (names : List String) :
    matchType bindings (.expr (("->" :: names).map Atom.sym))
        (.expr (("->" :: names).map Atom.sym)) = some bindings := by
  change matchReducedList bindings
      (("->" :: names).map Atom.sym) (("->" :: names).map Atom.sym) =
    some bindings
  exact matchReducedList_map_sym_self_from bindings hloop ("->" :: names)

/-- If a symbol has exactly one variable-free symbolic arrow type, casting the
operator head against that arrow succeeds with the empty theory.  This is the
concrete head-evaluation boundary used by selected-policy coincidence lemmas;
polymorphic signatures must instead expose their actual head bindings. -/
theorem mettaTypeCastAvoiding_symbolic_arrow
    (protectedScope : List VarName)
    (env : MinEnv) (world : World) (op : String) (names : List String)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (("->" :: names).map Atom.sym)]) :
    mettaTypeCastAvoiding protectedScope env world [] (.sym op)
        (.expr (("->" :: names).map Atom.sym)) = .inr [] := by
  unfold mettaTypeCastAvoiding
  dsimp only
  rw [hTypes]
  simp only [freshenArgumentTypes]
  have hFresh :
      freshenTypeCandidate
          (protectedScope ++
            typeCastInferenceAvoid env (typePrep world (.sym op)) (.sym op)
              (.expr (("->" :: names).map Atom.sym)) []
              [.expr (("->" :: names).map Atom.sym)]) 0
          (.expr (("->" :: names).map Atom.sym)) =
        .expr (("->" :: names).map Atom.sym) := by
    simp [freshenTypeCandidate, renameAllVars]
  rw [hFresh]
  simp only [matchExpectedType]
  rw [matchType_symbolic_arrow_self]

/-- Live-theory form of `mettaTypeCastAvoiding_symbolic_arrow`.  A
variable-free symbolic arrow contributes no new assignment, so operator-head
checking returns the complete incoming theory unchanged. -/
theorem mettaTypeCastAvoiding_symbolic_arrow_from
    (protectedScope : List VarName)
    (env : MinEnv) (world : World) (bindings : Bindings)
    (op : String) (names : List String)
    (hloop : Bindings.hasLoop bindings = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (("->" :: names).map Atom.sym)]) :
    mettaTypeCastAvoiding protectedScope env world bindings (.sym op)
        (.expr (("->" :: names).map Atom.sym)) = .inr bindings := by
  unfold mettaTypeCastAvoiding
  dsimp only
  rw [hTypes]
  simp only [freshenArgumentTypes]
  have hFresh :
      freshenTypeCandidate
          (protectedScope ++
            typeCastInferenceAvoid env (typePrep world (.sym op)) (.sym op)
              (.expr (("->" :: names).map Atom.sym)) bindings
              [.expr (("->" :: names).map Atom.sym)]) 0
          (.expr (("->" :: names).map Atom.sym)) =
            .expr (("->" :: names).map Atom.sym) := by
    simp [freshenTypeCandidate, renameAllVars]
  rw [hFresh]
  simp only [matchExpectedType]
  rw [matchType_symbolic_arrow_self_from bindings hloop]

/-- Local-boundary compatibility form of
`mettaTypeCastAvoiding_symbolic_arrow`. -/
theorem mettaTypeCast_symbolic_arrow
    (env : MinEnv) (world : World) (op : String) (names : List String)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (("->" :: names).map Atom.sym)]) :
    mettaTypeCast env world [] (.sym op)
        (.expr (("->" :: names).map Atom.sym)) = .inr [] := by
  exact mettaTypeCastAvoiding_symbolic_arrow [] env world op names hTypes

/-- Live-binding sibling of the all-`Atom`/`Bool` expected-selection theorem.
Quoted `Atom` formals and the ground `Bool` return check preserve the incoming
type theory exactly. -/
theorem selectFunctionTypeForExpectedFrom_atom_args_bool_selected_from
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (incoming : Bindings)
    (hloop : Bindings.hasLoop incoming = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])]) :
    selectFunctionTypeForExpectedFrom env world (.sym op) args (.sym "Bool") incoming =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym "Bool"
          typeBindings := incoming } := by
  apply Metta.selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
    env world op args (List.replicate args.length (.sym "Atom"))
      (.sym "Bool") (.sym "Bool") incoming incoming [] hTypes
  · simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_atom env world _ 0
      (applicationTypeInferenceScopeFrom (.sym "Bool") args incoming)
      incoming args
    intro j hj
    simp [hj]
  · simp [matchType, matchReduced, Metta.matchAtoms,
      Metta.matchAtomsWith, Bindings.merge, hloop]

/-- Live selection of an all-`Atom` arrow whose declared result is gradual.
Any concrete expected result is accepted by the `%Undefined%` return gate,
while the incoming applicability theory is retained exactly. -/
theorem selectFunctionTypeForExpectedFrom_atom_args_undefined_return_selected_from
    (env : MinEnv) (world : World) (op : String) (args : List Atom)
    (expected : Atom) (incoming : Bindings)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "%Undefined%"])]) :
    selectFunctionTypeForExpectedFrom env world (.sym op) args expected incoming =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym "%Undefined%"])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym "%Undefined%"
          typeBindings := incoming } := by
  apply Metta.selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
    env world op args (List.replicate args.length (.sym "Atom"))
      (.sym "%Undefined%") expected incoming incoming [] hTypes
  · simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_atom env world _ 0
      (applicationTypeInferenceScopeFrom expected args incoming)
      incoming args
    intro j hj
    simp [hj]
  · exact matchType_undefined_right incoming expected

/-- The live selected-application plan for a singleton monomorphic arrow whose
arguments are quoted `Atom`s.  The plan is executable data: applicability
preserves the incoming theory, and the closed operator arrow casts without
changing it.  Whether projecting that theory yields exactly one caller seed is
a separate consumer-side property. -/
def selectedApplicationExecutionPlan_atom_args_symbolic_return_from
    (env : MinEnv) (world : World) (op resultType : String)
    (args : List Atom) (incoming : Bindings)
    (hloop : Bindings.hasLoop incoming = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    SelectedApplicationExecutionPlan env world incoming op args where
  selected :=
    { functionType := .expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])
      argumentTypes := List.replicate args.length (.sym "Atom")
      returnType := .sym resultType
      typeBindings := incoming }
  scan := Metta.selectFunctionTypeForExpectedFrom_atom_args_undefined_selected_from
    env world op resultType args incoming hTypes
  headBindings := incoming
  headCast := by
    have hArrow :
        getTypes env (typePrep world (.sym op)) =
          [.expr (("->" ::
            (List.replicate args.length "Atom" ++ [resultType])).map Atom.sym)] := by
      simpa using hTypes
    simpa using
      (mettaTypeCastAvoiding_symbolic_arrow_from
        (expectedApplicationVisibleScope
          (.expr (.sym op :: args)) (.sym "%Undefined%"))
        env world incoming op
        (List.replicate args.length "Atom" ++ [resultType]) hloop hArrow)

/-- The live all-`Atom` plan exposes its selected payload definitionally. -/
@[simp] theorem selectedApplicationExecutionPlan_atom_args_symbolic_return_from_selected
    (env : MinEnv) (world : World) (op resultType : String)
    (args : List Atom) (incoming : Bindings)
    (hloop : Bindings.hasLoop incoming = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    (selectedApplicationExecutionPlan_atom_args_symbolic_return_from
      env world op resultType args incoming hloop hTypes).selected =
      { functionType := .expr (.sym "->" ::
          List.replicate args.length (.sym "Atom") ++ [.sym resultType])
        argumentTypes := List.replicate args.length (.sym "Atom")
        returnType := .sym resultType
        typeBindings := incoming } := rfl

/-- Live selected plan for the closed gradual `let`-shaped arrow.  The
incoming theory is retained exactly by applicability and by operator-head
checking; seed normalization remains an explicit caller obligation. -/
def selectedApplicationExecutionPlan_let_policy_from
    (env : MinEnv) (world : World) (op : String)
    (pattern payload template : Atom) (incoming : Bindings)
    (hloop : Bindings.hasLoop incoming = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    SelectedApplicationExecutionPlan env world incoming op
      [pattern, payload, template] where
  selected :=
    { functionType := .expr
        [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
          .sym "%Undefined%"]
      argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      returnType := .sym "%Undefined%"
      typeBindings := incoming }
  scan := Metta.selectFunctionTypeForExpectedFrom_let_policy_selected_from
    env world op pattern payload template incoming hTypes
  headBindings := incoming
  headCast := by
    simpa using
      (mettaTypeCastAvoiding_symbolic_arrow_from
        (expectedApplicationVisibleScope
          (.expr [.sym op, pattern, payload, template]) (.sym "%Undefined%"))
        env world incoming op
        ["Atom", "%Undefined%", "Atom", "%Undefined%"] hloop
        (by simpa using hTypes))

/-- Live selected plan for one variable-free symbolic arrow whose concrete
argument scan succeeds from the evaluator's incoming theory.  Unlike the
specialized all-`Atom` and `let` constructors, this boundary accepts the
complete detailed scan equation: typed consumers retain latent diagnostics
and cannot replace the live theory with an empty-seed compatibility result. -/
def selectedApplicationExecutionPlan_symbolic_arrow_from_detailed
    (env : MinEnv) (world : World) (op : String)
    (args : List Atom) (argTypeNames : List String) (resultType : String)
    (incoming typeBindings : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" :: argTypeNames.map Atom.sym ++ [.sym resultType])])
    (hArity : args.length = argTypeNames.length)
    (hDetailed : typeCheckArgsDetailedOutcomeScoped env world
      (argTypeNames.map Atom.sym)
      (applicationTypeInferenceScopeFrom (.sym "%Undefined%") args incoming)
      0 incoming args = .success typeBindings latentErrors)
    (hloop : Bindings.hasLoop typeBindings = false) :
    SelectedApplicationExecutionPlan env world incoming op args where
  selected :=
    { functionType := .expr
        (.sym "->" :: argTypeNames.map Atom.sym ++ [.sym resultType])
      argumentTypes := argTypeNames.map Atom.sym
      returnType := .sym resultType
      typeBindings := typeBindings }
  scan := by
    apply Metta.selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
      env world op args (argTypeNames.map Atom.sym) (.sym resultType)
        (.sym "%Undefined%")
        incoming typeBindings latentErrors hTypes
    · simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
        renameAllVars]
    · simpa using hArity
    · exact hDetailed
    · exact matchType_undefined_left typeBindings (.sym resultType)
  headBindings := typeBindings
  headCast := by
    simpa using
      (mettaTypeCastAvoiding_symbolic_arrow_from
        (expectedApplicationVisibleScope
          (.expr (.sym op :: args)) (.sym "%Undefined%"))
        env world typeBindings op (argTypeNames ++ [resultType]) hloop
        (by simpa using hTypes))

/-- Typed lazy-ternary specialization of the detailed symbolic-arrow plan.
The selected theory and its public seed remain explicit: a consumer may use
this constructor only after proving the concrete live scan and projection
equations for its incoming evaluator bindings. -/
def evalQuotedQuotedApplicationExecutionPlan_symbolic_from_detailed
    (env : MinEnv) (world : World) (incoming : Bindings)
    (op : String) (cond thenBranch elseBranch : Atom)
    (typeBindings : Bindings) (latentErrors : List TypeCheckArgsError)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr [.sym "->", .sym "Bool", .sym "Atom", .sym "Atom",
        .sym "%Undefined%"]])
    (hDetailed : typeCheckArgsDetailedOutcomeScoped env world
      [.sym "Bool", .sym "Atom", .sym "Atom"]
      (applicationTypeInferenceScopeFrom (.sym "%Undefined%")
        [cond, thenBranch, elseBranch] incoming)
      0 incoming [cond, thenBranch, elseBranch] =
        .success typeBindings latentErrors)
    (hloop : Bindings.hasLoop typeBindings = false)
    (hSeed :
      (selectedApplicationExecutionPlan_symbolic_arrow_from_detailed
        env world op [cond, thenBranch, elseBranch]
          ["Bool", "Atom", "Atom"] "%Undefined%" incoming typeBindings
          latentErrors (by simpa using hTypes) (by simp) hDetailed hloop).seeds =
        [incoming]) :
    EvalQuotedQuotedApplicationExecutionPlan env world incoming op
      [cond, thenBranch, elseBranch] (.sym "Bool") where
  plan := selectedApplicationExecutionPlan_symbolic_arrow_from_detailed
    env world op [cond, thenBranch, elseBranch]
      ["Bool", "Atom", "Atom"] "%Undefined%" incoming typeBindings
      latentErrors (by simpa using hTypes) (by simp) hDetailed hloop
  seedSingleton := hSeed
  argumentPolicies_eq := by
    have hBool := instantiate_of_closed typeBindings (.sym "Bool")
      (by simp [Atom.vars])
    have hAtom := instantiate_of_closed typeBindings (.sym "Atom")
      (by simp [Atom.vars])
    change
      [ ((instantiate typeBindings (.sym "Bool") != .sym "Atom") &&
            (instantiate typeBindings (.sym "Bool") != .sym "Variable") &&
            (instantiate typeBindings (.sym "Bool") != .sym "Expression"),
          instantiate typeBindings (.sym "Bool"))
      , ((instantiate typeBindings (.sym "Atom") != .sym "Atom") &&
            (instantiate typeBindings (.sym "Atom") != .sym "Variable") &&
            (instantiate typeBindings (.sym "Atom") != .sym "Expression"),
          instantiate typeBindings (.sym "Atom"))
      , ((instantiate typeBindings (.sym "Atom") != .sym "Atom") &&
            (instantiate typeBindings (.sym "Atom") != .sym "Variable") &&
            (instantiate typeBindings (.sym "Atom") != .sym "Expression"),
          instantiate typeBindings (.sym "Atom")) ] =
        [(true, .sym "Bool"), (false, .sym "Atom"), (false, .sym "Atom")]
    rw [hBool, hAtom]
    rfl
  returnIsAtom_eq := by
    have hUndefined :=
      instantiate_of_closed typeBindings (.sym "%Undefined%")
        (by simp [Atom.vars])
    change (instantiate typeBindings (.sym "%Undefined%") == .sym "Atom") = false
    rw [hUndefined]
    rfl
  resultExpected_eq := by
    have hUndefined :=
      instantiate_of_closed typeBindings (.sym "%Undefined%")
        (by simp [Atom.vars])
    change (if instantiate typeBindings (.sym "%Undefined%") == .sym "Expression"
      then .sym "%Undefined%" else instantiate typeBindings (.sym "%Undefined%")) =
        .sym "%Undefined%"
    rw [hUndefined]
    rfl

@[simp] theorem selectedApplicationExecutionPlan_let_policy_from_selected
    (env : MinEnv) (world : World) (op : String)
    (pattern payload template : Atom) (incoming : Bindings)
    (hloop : Bindings.hasLoop incoming = false)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    (selectedApplicationExecutionPlan_let_policy_from env world op
      pattern payload template incoming hloop hTypes).selected =
      { functionType := .expr
          [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
            .sym "%Undefined%"]
        argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
        returnType := .sym "%Undefined%"
        typeBindings := incoming } := rfl

/-- Complete ordinary-plan evidence for a monomorphic symbolic arrow whose
arguments are all quoted `Atom`s.  This packages the exact live scan,
binding-neutral operator-head cast, and singleton empty seed once; concrete
operator suppliers need not unfold the shared executor. -/
theorem applicationPlanCorresponds_atom_args_symbolic_return_selected
    (env : MinEnv) (world : World) (op resultType : String)
    (args : List Atom)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])])
    (hSelected : selectFunctionType env world (.sym op) args =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym resultType])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym resultType
          typeBindings := [] }) :
    ApplicationPlanCorresponds [] (.selected
      { functionType := .expr (.sym "->" ::
          List.replicate args.length (.sym "Atom") ++ [.sym resultType])
        argumentTypes := List.replicate args.length (.sym "Atom")
        returnType := .sym resultType
        typeBindings := [] }
      hSelected) := by
  apply ApplicationPlanCorresponds.ofSelected
    (Metta.selectFunctionTypeForExpectedFrom_atom_args_undefined_selected
      env world op resultType args hTypes) []
  · have hArrow :
        getTypes env (typePrep world (.sym op)) =
          [.expr (("->" ::
            (List.replicate args.length "Atom" ++ [resultType])).map Atom.sym)] := by
      simpa using hTypes
    simpa using
      (mettaTypeCastAvoiding_symbolic_arrow
        (expectedApplicationVisibleScope
          (.expr (.sym op :: args)) (.sym "%Undefined%"))
        env world op
        (List.replicate args.length "Atom" ++ [resultType]) hArrow)
  · simp

/-- Any exact raw policy for the same singleton monomorphic arrow is the
selected policy above and therefore carries the corresponding shared-plan
evidence.  The impossible tuple constructor is eliminated from the raw scan
equation rather than by inspecting projection fields. -/
theorem ExactApplicationPolicy.applicationPlanCorresponds_atom_args_symbolic_return
    {env : MinEnv} {world : World} {op resultType : String}
    {args : List Atom}
    (policy : ExactApplicationPolicy env world op args)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    ApplicationPlanCorresponds [] policy := by
  let canonical : SelectedFunctionType :=
    { functionType := .expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])
      argumentTypes := List.replicate args.length (.sym "Atom")
      returnType := .sym resultType
      typeBindings := [] }
  have hCanonical :
      selectFunctionType env world (.sym op) args = .selected canonical := by
    simpa [canonical] using
      (Metta.selectFunctionType_atom_args_symbolic_return_selected
        env world op resultType args hTypes)
  cases policy with
  | selected selected hSelected =>
      have hEq : selected = canonical := by
        rw [hCanonical] at hSelected
        exact FunctionTypeScanOutcome.selected.inj hSelected.symm
      subst selected
      exact applicationPlanCorresponds_atom_args_symbolic_return_selected
        env world op resultType args hTypes hSelected
  | untypedTuple hScan =>
      rw [hCanonical] at hScan
      contradiction

/-- Plan evidence for the quoted-arguments/Boolean-result compatibility
carrier.  The carrier's selected payload is identified from the deterministic
raw scan; no syntactic unfolding of a concrete supplier is required. -/
theorem QuotedBoolApplicationPolicy.applicationPlanCorresponds
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (policy : QuotedBoolApplicationPolicy env world op args)
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])]) :
    ApplicationPlanCorresponds []
      (.selected policy.decision.selectedType policy.selected_eq) := by
  let canonical : SelectedFunctionType :=
    { functionType := .expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])
      argumentTypes := List.replicate args.length (.sym "Atom")
      returnType := .sym "Bool"
      typeBindings := [] }
  have hCanonical : selectFunctionType env world (.sym op) args =
      .selected canonical := by
    simpa [canonical] using
      (Metta.selectFunctionType_atom_args_symbolic_return_selected
        env world op "Bool" args hTypes)
  have hSelectedType : policy.decision.selectedType = canonical := by
    have hEq := policy.selected_eq
    rw [hCanonical] at hEq
    exact FunctionTypeScanOutcome.selected.inj hEq.symm
  apply ApplicationPlanCorresponds.ofSelected
    (by simpa [hSelectedType, canonical] using
      (Metta.selectFunctionTypeForExpectedFrom_atom_args_undefined_selected
        env world op "Bool" args hTypes)) []
  · have hArrow : getTypes env (typePrep world (.sym op)) =
        [.expr (("->" ::
          (List.replicate args.length "Atom" ++ ["Bool"])).map Atom.sym)] := by
      simpa using hTypes
    simpa [hSelectedType, canonical] using
      (mettaTypeCastAvoiding_symbolic_arrow
        (expectedApplicationVisibleScope
          (.expr (.sym op :: args)) (.sym "%Undefined%"))
        env world op (List.replicate args.length "Atom" ++ ["Bool"])
        hArrow)
  · simp

/-- Any exact raw policy for the concrete `let` signature carries the same
shared ordinary-plan evidence.  This is the mixed quoted/evaluated companion
to `applicationPlanCorresponds_atom_args_symbolic_return`. -/
theorem ExactApplicationPolicy.applicationPlanCorresponds_let_policy
    {env : MinEnv} {world : World} {op : String}
    {pattern payload template : Atom}
    (policy : ExactApplicationPolicy env world op
      [pattern, payload, template])
    (hTypes : getTypes env (typePrep world (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    ApplicationPlanCorresponds [] policy := by
  let canonical : SelectedFunctionType :=
    { functionType := .expr
        [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
          .sym "%Undefined%"]
      argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      returnType := .sym "%Undefined%"
      typeBindings := [] }
  have hCanonical : selectFunctionType env world (.sym op)
      [pattern, payload, template] = .selected canonical := by
    simpa [canonical] using
      (Metta.selectFunctionType_let_policy_selected env world op
        pattern payload template hTypes)
  cases policy with
  | selected selected hSelected =>
      have hEq : selected = canonical := by
        rw [hCanonical] at hSelected
        exact FunctionTypeScanOutcome.selected.inj hSelected.symm
      subst selected
      apply ApplicationPlanCorresponds.ofSelected
        (by simpa [canonical] using
          (Metta.selectFunctionTypeForExpectedFrom_let_policy_selected
            env world op pattern payload template hTypes)) []
      · have hArrow : getTypes env (typePrep world (.sym op)) =
            [.expr (["->", "Atom", "%Undefined%", "Atom",
              "%Undefined%"].map Atom.sym)] := by
          simpa using hTypes
        simpa [canonical] using
          (mettaTypeCastAvoiding_symbolic_arrow
            (expectedApplicationVisibleScope
              (.expr [.sym op, pattern, payload, template])
              (.sym "%Undefined%"))
            env world op ["Atom", "%Undefined%", "Atom", "%Undefined%"]
            hArrow)
      · simp
  | untypedTuple hScan =>
      rw [hCanonical] at hScan
      contradiction

/-- Ordinary and expected-aware evaluation coincide at a concrete application when their scans
select the same complete policy.  The hypotheses expose the path-sensitive fact explicitly; no
post-hoc result-filtering equivalence is assumed. -/
theorem mettaEvalExpected_eq_mettaEval_of_same_selected
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (expected : Atom) (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (selected : SelectedFunctionType)
    (hOrdinary : selectFunctionType env st.world (.sym op) args = .selected selected)
    (ordinaryPlan : ApplicationPlanCorresponds []
      (.selected selected hOrdinary))
    (hExpectedSelected :
      selectFunctionTypeForExpected env st.world (.sym op) args expected =
        .selected selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world selected.typeBindings (.sym op)
      selected.functionType = .inr headBindings)
    (hInitial : selectedApplicationInitialBindingsFromTheory []
      (.expr (.sym op :: args)) expected headBindings = [[]]) :
    mettaEvalExpected env (fuel + 1) st [] (.expr (.sym op :: args)) expected =
      mettaEval env (fuel + 1) st [] (.expr (.sym op :: args)) := by
  rw [mettaEvalExpected_eq_evaluateExpectedApplication_of_selected
    env fuel st op args expected hExpected hNeedsInterpret hNotError selected
      hExpectedSelected headBindings hHead hInitial]
  rw [mettaEval_eq_evaluateExpectedApplication_of_selected
    env fuel st op args selected hNotError hOrdinary ordinaryPlan]

/-- A singleton arrow with raw return type `%Undefined%` selects the same complete policy in
ordinary and expected-aware evaluation.  This is a scan-characterization boundary, not a global
coincidence claim: callers must provide the concrete declaration list, arity, and successful
argument-check equations that determine both paths. -/
theorem mettaEvalExpected_eq_mettaEval_of_singleton_undefined_return
    (env : MinEnv) (fuel : Nat) (st : St) (op : String)
    (args argTypes : List Atom) (typeBindings : Bindings)
    (latentErrors : List TypeCheckArgsError) (expected : Atom)
    (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hTypes : getTypes env (typePrep st.world (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])])
    (hFresh : freshenFunctionTypeCandidates env
        (.expr (.sym op :: args)) args expected
        [.expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])] =
      [.expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])])
    (hArity : args.length = argTypes.length)
    (hCheck : typeCheckArgsOutcome env st.world argTypes 0 [] args =
      .success typeBindings)
    (hOrdinaryLive :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args
          (.sym "%Undefined%") [] =
        .selected
          { functionType := .expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])
            argumentTypes := argTypes
            returnType := .sym "%Undefined%"
            typeBindings := typeBindings })
    (ordinaryHeadBindings : Bindings)
    (hOrdinaryHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args))
        (.sym "%Undefined%"))
      env st.world typeBindings (.sym op)
      (.expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])) =
        .inr ordinaryHeadBindings)
    (hOrdinarySeed : selectedApplicationInitialBindingsFromTheory []
      (.expr (.sym op :: args)) (.sym "%Undefined%") ordinaryHeadBindings =
        [[]])
    (hExpectedCheck : typeCheckArgsDetailedOutcomeScoped env st.world argTypes
      (applicationTypeInferenceScope expected args) 0 [] args =
        .success typeBindings latentErrors)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world typeBindings (.sym op)
      (.expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])) =
        .inr headBindings)
    (hInitial : selectedApplicationInitialBindingsFromTheory []
      (.expr (.sym op :: args)) expected headBindings = [[]]) :
    mettaEvalExpected env (fuel + 1) st [] (.expr (.sym op :: args)) expected =
      mettaEval env (fuel + 1) st [] (.expr (.sym op :: args)) := by
  let selected : SelectedFunctionType :=
    { functionType := .expr (.sym "->" :: argTypes ++ [.sym "%Undefined%"])
      argumentTypes := argTypes
      returnType := .sym "%Undefined%"
      typeBindings := typeBindings }
  have hOrdinary :
      selectFunctionType env st.world (.sym op) args = .selected selected := by
    simpa [selected] using
      (selectFunctionType_singleton_arrow_selected_of_outcome
        env st.world op args argTypes (.sym "%Undefined%") typeBindings
        hTypes hArity hCheck)
  have hExpectedSelected :
      selectFunctionTypeForExpected env st.world (.sym op) args expected =
        .selected selected := by
    simpa [selected] using
      (selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed
        env st.world op args argTypes (.sym "%Undefined%") expected typeBindings
        latentErrors hTypes hFresh hArity hExpectedCheck
        (matchType_undefined_right typeBindings expected))
  have ordinaryPlan : ApplicationPlanCorresponds []
      (.selected selected hOrdinary) := by
    constructor
    · simpa [ExactApplicationPolicy.planScanOutcome, selected] using hOrdinaryLive
    · simp only [ExactApplicationPolicy.headSeedCorresponds]
      exact ⟨ordinaryHeadBindings, by simpa [selected] using hOrdinaryHead,
        hOrdinarySeed⟩
  exact mettaEvalExpected_eq_mettaEval_of_same_selected
    env fuel st op args expected hExpected hNeedsInterpret hNotError selected hOrdinary
      ordinaryPlan hExpectedSelected headBindings
        (by simpa [selected] using hHead) hInitial

@[simp] theorem argMask_untypedTuple (arity : Nat) :
    argMask (untypedTupleSelectedType arity) arity = List.replicate arity true := by
  rw [← argumentEvaluationPolicies_map_fst, argumentEvaluationPolicies_untypedTuple]
  simp

theorem mettaEval_eq_evaluateSelectedApplication_of_untypedTuple
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hScan : selectFunctionType env st.world (.sym op) args = .exhausted [] true)
    (planCorresponds : ApplicationPlanCorresponds [] (.untypedTuple hScan)) :
    mettaEval env (fuel + 1) st [] (Atom.expr (Atom.sym op :: args)) =
      prioritizeSemanticResults (evaluateSelectedApplication
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := [] }] [])
        st op args (List.replicate args.length true) false) := by
  conv_lhs => unfold mettaEval
  rw [instantiate_nil (Atom.expr (Atom.sym op :: args))]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  have hLiveScan :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args
          (.sym "%Undefined%") [] = .exhausted [] true := by
    simpa [ExactApplicationPolicy.planScanOutcome] using planCorresponds.scan
  rw [executeApplicationPlan, hLiveScan]
  simp only [↓reduceIte, List.map_nil, List.append_nil,
    Prod.eta]
  change prioritizeSemanticResults (evaluateExpectedApplication
      (mettaEvalExpected env fuel)
      (fun nextSt application =>
        interpretFuel env (fuel + 1) nextSt
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
             bnd := [] }] [])
      st op args (untypedTupleSelectedType args.length)) =
    prioritizeSemanticResults (evaluateSelectedApplication
      (mettaEval env fuel)
      (fun nextSt application =>
        interpretFuel env (fuel + 1) nextSt
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
             bnd := [] }] [])
      st op args (List.replicate args.length true) false)
  apply congrArg prioritizeSemanticResults
  simpa only [evaluateExpectedApplication, argMask_untypedTuple,
      returnsAtom_untypedTuple] using
    (evaluateExpectedApplication_eq_evaluateSelectedApplication_of_recursionNeutral
      (mettaEvalExpected env fuel) (mettaEval env fuel)
      (fun nextSt application =>
        interpretFuel env (fuel + 1) nextSt
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
             bnd := [] }] [])
      st op args (untypedTupleSelectedType args.length)
        (selectedApplicationRecursionNeutral_untypedTuple args.length)
        (mettaEvalExpected_undefined env fuel))

/-- Membership in a left-to-right state fold that appends each branch's
outputs comes either from the initial prefix or from one concrete branch.
The witness retains the state at which that branch ran; no independent-state
fiction is introduced. -/
theorem mem_foldl_append_state
    {Input Output State : Type}
    (run : State → Input → List Output × State)
    (inputs : List Input) (prior : List Output) (state : State)
    (output : Output)
    (hmem : output ∈
      (inputs.foldl (fun acc input =>
        let next := run acc.2 input
        (acc.1 ++ next.1, next.2)) (prior, state)).1) :
    output ∈ prior ∨
      ∃ input ∈ inputs, ∃ branchState,
        output ∈ (run branchState input).1 := by
  induction inputs generalizing prior state with
  | nil =>
      exact Or.inl (by simpa using hmem)
  | cons input inputs ih =>
      cases hrun : run state input with
      | mk branchOutputs nextState =>
          have htail : output ∈
              (inputs.foldl (fun acc nextInput =>
                let next := run acc.2 nextInput
                (acc.1 ++ next.1, next.2))
                (prior ++ branchOutputs, nextState)).1 := by
            simpa [hrun] using hmem
          rcases ih (prior := prior ++ branchOutputs)
              (state := nextState) htail with hprior | hlater
          · rcases List.mem_append.mp hprior with hinitial | hbranch
            · exact Or.inl hinitial
            · exact Or.inr ⟨input, by simp, state, by simpa [hrun] using hbranch⟩
          · rcases hlater with ⟨laterInput, hlaterInput, branchState, hresult⟩
            exact Or.inr
              ⟨laterInput, by simp [hlaterInput], branchState, hresult⟩

/-- Invariant-aware form of `mem_foldl_append_state`.  The invariant is
required at the initial state and preserved by every branch, so the extracted
branch-entry state is certified without pretending that alternatives run from
independent copies of the initial state. -/
theorem mem_foldl_append_state_of_invariant
    {Input Output State : Type}
    (run : State → Input → List Output × State)
    (inputs : List Input) (prior : List Output) (state : State)
    (output : Output) (P : State → Prop)
    (hInitial : P state)
    (hStep : ∀ branchState input,
      P branchState → P (run branchState input).2)
    (hmem : output ∈
      (inputs.foldl (fun acc input =>
        let next := run acc.2 input
        (acc.1 ++ next.1, next.2)) (prior, state)).1) :
    output ∈ prior ∨
      ∃ input ∈ inputs, ∃ branchState,
        P branchState ∧ output ∈ (run branchState input).1 := by
  induction inputs generalizing prior state with
  | nil =>
      exact Or.inl (by simpa using hmem)
  | cons input inputs ih =>
      cases hrun : run state input with
      | mk branchOutputs nextState =>
          have hNext : P nextState := by
            have := hStep state input hInitial
            simpa [hrun] using this
          have htail : output ∈
              (inputs.foldl (fun acc nextInput =>
                let next := run acc.2 nextInput
                (acc.1 ++ next.1, next.2))
                (prior ++ branchOutputs, nextState)).1 := by
            simpa [hrun] using hmem
          rcases ih (prior := prior ++ branchOutputs)
              (state := nextState) hNext htail with hprior | hlater
          · rcases List.mem_append.mp hprior with hinitial | hbranch
            · exact Or.inl hinitial
            · exact Or.inr
                ⟨input, by simp, state, hInitial, by simpa [hrun] using hbranch⟩
          · rcases hlater with
              ⟨laterInput, hlaterInput, branchState, hP, hresult⟩
            exact Or.inr
              ⟨laterInput, by simp [hlaterInput], branchState, hP, hresult⟩

/-- Every result of the ordered applicability-seed fold comes from one seed
that was actually emitted, evaluated at the state reached after all earlier
seeds. -/
theorem mem_evaluateExpectedApplicationSeeds
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : Bindings → St → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : List Bindings) (st : St)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (result : Atom × Bindings)
    (hmem : result ∈
      (evaluateExpectedApplicationSeeds evalRecursive reduceApplication
        initialBindings st op args selected).1) :
    ∃ bindings ∈ initialBindings, ∃ branchState,
      result ∈
        (evaluateExpectedApplicationFrom evalRecursive
          (reduceApplication bindings) bindings branchState op args selected).1 := by
  unfold evaluateExpectedApplicationSeeds at hmem
  have hextract := mem_foldl_append_state
    (fun branchState bindings =>
      evaluateExpectedApplicationFrom evalRecursive
        (reduceApplication bindings) bindings branchState op args selected)
    initialBindings [] st result hmem
  rcases hextract with himpossible | hextract
  · simp at himpossible
  · exact hextract

/-- Invariant-aware selected-seed extraction.  Every seed runs after all
earlier seeds, and the witness carries the invariant at that exact
chronology-local branch-entry state. -/
theorem mem_evaluateExpectedApplicationSeeds_of_invariant
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : Bindings → St → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : List Bindings) (st : St)
    (op : String) (args : List Atom) (selected : SelectedFunctionType)
    (result : Atom × Bindings) (P : St → Prop)
    (hInitial : P st)
    (hStep : ∀ branchState bindings,
      P branchState →
        P (evaluateExpectedApplicationFrom evalRecursive
          (reduceApplication bindings) bindings branchState op args selected).2)
    (hmem : result ∈
      (evaluateExpectedApplicationSeeds evalRecursive reduceApplication
        initialBindings st op args selected).1) :
    ∃ bindings ∈ initialBindings, ∃ branchState,
      P branchState ∧
      result ∈
        (evaluateExpectedApplicationFrom evalRecursive
          (reduceApplication bindings) bindings branchState op args selected).1 := by
  unfold evaluateExpectedApplicationSeeds at hmem
  have hextract := mem_foldl_append_state_of_invariant
    (fun branchState bindings =>
      evaluateExpectedApplicationFrom evalRecursive
        (reduceApplication bindings) bindings branchState op args selected)
    initialBindings [] st result P hInitial hStep hmem
  rcases hextract with himpossible | hextract
  · simp at himpossible
  · exact hextract

/-- A non-error readout from an exactly selected live application certifies
that operator-head checking took its success branch.  This extracts the
runtime datum needed to build `SelectedApplicationExecutionPlan`; it does not
assume that the resulting public seeds are singleton or equal to `incoming`.
-/
theorem mettaEval_nonerror_mem_implies_headCast_success_of_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (incoming : Bindings)
    (source : Atom) (op : String) (args : List Atom)
    (selected : SelectedFunctionType)
    (hInstantiate : instantiate incoming source =
      Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hScan : selectFunctionTypeForExpectedFrom env st.world (.sym op) args
      (.sym "%Undefined%") incoming = .selected selected)
    (result : Atom × Bindings) (hResultNotError : result.1.isError = false)
    (hmem : result ∈ (mettaEval env (fuel + 1) st incoming source).1) :
    ∃ headBindings,
      mettaTypeCastAvoiding
          (expectedApplicationVisibleScope
            (.expr (.sym op :: args)) (.sym "%Undefined%"))
          env st.world selected.typeBindings (.sym op) selected.functionType =
        .inr headBindings := by
  cases hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope
        (.expr (.sym op :: args)) (.sym "%Undefined%"))
      env st.world selected.typeBindings (.sym op) selected.functionType with
  | inr headBindings =>
      exact ⟨headBindings, rfl⟩
  | inl rejected =>
      conv at hmem =>
        lhs
        unfold mettaEval
      rw [hInstantiate] at hmem
      have hNotEmpty :
          (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
      simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte] at hmem
      rw [executeApplicationPlan, hScan] at hmem
      simp only [executeSelectedApplicationPlan, hHead] at hmem
      have hraw := mem_of_mem_prioritizeSemanticResults hmem
      rcases List.mem_flatMap.mp hraw with
        ⟨seed, _hseed, hRejected⟩
      rcases List.mem_map.mp hRejected with
        ⟨actual, _hactual, hResult⟩
      rw [← hResult] at hResultNotError
      simp [badTypeAtom, Atom.isError] at hResultNotError

/-- The live selected-application boundary after an incoming binding has
instantiated the source application.  This is the authoritative equation:
the operator-head cast may emit zero, one, or several public seeds, and each
seed is used for both argument evaluation and rule reduction. -/
theorem mettaEval_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args) :
    mettaEval env (fuel + 1) st bnd source =
      prioritizeSemanticResults (evaluateExpectedApplicationSeeds
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun bindings nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bindings }] [])
        plan.seeds st op args plan.selected) := by
  conv_lhs => unfold mettaEval
  rw [hInstantiate]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rw [executeApplicationPlan, plan.scan]
  simp only [executeSelectedApplicationPlan, plan.headCast]
  rfl

/-- Ordinary and expected-aware live evaluation coincide when both paths
select the same complete policy, the source is stable after caller
instantiation, and operator-head checking produces the same public seed
family.  These equations are deliberately explicit: expectedness changes the
selection path, so equality cannot be recovered by post-filtering results. -/
theorem mettaEvalExpected_eq_mettaEval_of_same_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom) (expected : Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hStable : instantiate bnd (Atom.expr (Atom.sym op :: args)) =
      Atom.expr (Atom.sym op :: args))
    (hExpected : (expected == .sym "%Undefined%") = false)
    (hNeedsInterpret :
      (expected == Atom.atomType || expected == Atom.expressionType) = false)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (hExpectedSelected :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args expected bnd =
        .selected plan.selected)
    (headBindings : Bindings)
    (hHead : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr (.sym op :: args)) expected)
      env st.world plan.selected.typeBindings (.sym op)
      plan.selected.functionType = .inr headBindings)
    (hSeeds : selectedApplicationInitialBindingsFromTheory bnd
      (.expr (.sym op :: args)) expected headBindings = plan.seeds) :
    mettaEvalExpected env (fuel + 1) st bnd source expected =
      mettaEval env (fuel + 1) st bnd source := by
  rw [mettaEvalExpected_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    env fuel st bnd source op args expected hInstantiate hStable hExpected
      hNeedsInterpret hNotError plan.selected hExpectedSelected headBindings hHead]
  rw [mettaEval_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    env fuel st bnd source op args hInstantiate hNotError plan]
  rw [hSeeds]

/-- Membership form of the authoritative live selected-application equation.
The witness identifies the concrete public seed and its chronology-local
starting state. -/
theorem mettaEval_mem_implies_evaluateExpectedApplicationFrom_of_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (result : Atom × Bindings)
    (hmem : result ∈ (mettaEval env (fuel + 1) st bnd source).1) :
    ∃ seed ∈ plan.seeds, ∃ branchState,
      result ∈
        (evaluateExpectedApplicationFrom
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          (fun nextSt application =>
            interpretFuel env (fuel + 1) nextSt
              [{ stack := atomToStack
                  (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
          seed branchState op args plan.selected).1 := by
  rw [mettaEval_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    env fuel st bnd source op args hInstantiate hNotError plan] at hmem
  have hraw := mem_of_mem_prioritizeSemanticResults hmem
  exact mem_evaluateExpectedApplicationSeeds
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    (fun bindings nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := bindings }] [])
    plan.seeds st op args plan.selected result hraw

/-- Singleton-seed specialization of
`mettaEval_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate`.
The premise remains explicit because nonempty live theories need not normalize
to one syntactically identical seed. -/
theorem mettaEval_eq_evaluateExpectedApplication_of_selected_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (hSeed : plan.seeds = [bnd]) :
    mettaEval env (fuel + 1) st bnd source =
      prioritizeSemanticResults (evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bnd }] [])
        bnd st op args plan.selected) := by
  conv_lhs => unfold mettaEval
  rw [hInstantiate]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rw [executeApplicationPlan, plan.scan]
  simp only [executeSelectedApplicationPlan, plan.headCast]
  rw [show selectedApplicationInitialBindingsFromTheory bnd
      (.expr (.sym op :: args)) (.sym "%Undefined%") plan.headBindings =
        plan.seeds by rfl, hSeed]
  simp only [evaluateExpectedApplicationSeeds, List.foldl_cons, List.foldl_nil,
    List.nil_append]

/-- Membership form of the exact live all-quoted selected-application bridge.

The root reducer may return additional readouts, so the selected root is a
membership premise rather than a singleton equation.  Recursive result
evaluation may retain public bindings; both runtime projections therefore
remain explicit in the conclusion. -/
theorem mettaEval_expr_mem_of_instantiated_all_quoted_and_root_eval_member_bnd
    (env : MinEnv) (fuel : Nat) (st : St)
    (bnd : Bindings) (source : Atom) (op : String) (args : List Atom)
    (root final : Atom) (rootBnd finalBnd : Bindings)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (hInst : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hSeed : plan.seeds = [bnd])
    (hMask : argMask plan.selected args.length =
      List.replicate args.length false)
    (hReturn : returnsAtom plan.selected = false)
    (hResultExpected :
      selectedResultExpected plan.selected = Atom.sym "%Undefined%")
    (hNoError :
      (((args.map (instantiate bnd)).zip args).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval",
              Atom.expr (Atom.sym op :: args.map (instantiate bnd))]) [],
           bnd := bnd }] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf :
      (root == Atom.expr (Atom.sym op :: args.map (instantiate bnd))) = false)
    (hFinal : ∀ st0,
      (final, finalBnd) ∈
        (mettaEval env fuel st0
          (restrictBnd
            (expectedApplicationRetentionScope bnd args)
            ((Bindings.merge bnd rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd
          (expectedApplicationRetentionScope bnd args)
          ((Bindings.merge
            (restrictBnd
              (expectedApplicationRetentionScope bnd args)
              ((Bindings.merge bnd rootBnd).head?.getD rootBnd))
            finalBnd).head?.getD finalBnd)) ∈
      (mettaEval env (fuel + 1) st bnd source).1 := by
  rw [mettaEval_eq_evaluateExpectedApplication_of_selected_after_instantiate
    env fuel st bnd source op args hInst hNotError plan hSeed]
  rw [evaluateExpectedApplicationFrom_eq_factored]
  rw [evaluateExpectedApplicationFromFactored_all_quoted_eq_mettaEvalExprPartFoldStep
    env fuel st bnd op args plan.selected false hMask hReturn
      (fun _ => hResultExpected) hNoError]
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := hFinalNotError)
  unfold mettaEvalExprPartFoldStep
  rw [hNoError]
  simp only [List.nil_append]
  cases hpairs : interpretFuel env (fuel + 1) st
      [{ stack := atomToStack
          (Atom.expr [Atom.sym "eval",
            Atom.expr (Atom.sym op :: args.map (instantiate bnd))]) [],
         bnd := bnd }] [] with
  | mk pairs stRoot =>
      have hRootPairs : (root, rootBnd) ∈ pairs := by
        rw [hpairs] at hRoot
        exact hRoot
      have hfold :=
        mettaEval_expr_root_evals_selected_readout_all_states_bnd
          env fuel (expectedApplicationRetentionScope bnd args)
          (Atom.expr (Atom.sym op :: args.map (instantiate bnd))) bnd false
          (root, rootBnd) pairs stRoot final finalBnd hRootPairs
          hRootNotNotReducible hRootNotSelf rfl hFinal
      simpa using hfold

theorem mettaEval_eq_evaluateSelectedApplication_of_untypedTuple_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hScan : selectFunctionType env st.world (.sym op) args = .exhausted [] true)
    (planCorresponds : ApplicationPlanCorresponds bnd (.untypedTuple hScan)) :
    mettaEval env (fuel + 1) st bnd source =
      prioritizeSemanticResults (evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bnd }] [])
        bnd st op args (untypedTupleSelectedTypeFrom bnd args.length)) := by
  conv_lhs => unfold mettaEval
  rw [hInstantiate]
  have hNotEmpty : (Atom.expr (Atom.sym op :: args) == emptyA) = false := rfl
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  have hLiveScan :
      selectFunctionTypeForExpectedFrom env st.world (.sym op) args
          (.sym "%Undefined%") bnd = .exhausted [] true := by
    simpa [ExactApplicationPolicy.planScanOutcome] using planCorresponds.scan
  rw [executeApplicationPlan, hLiveScan]
  simp [untypedTupleSelectedTypeFrom]

theorem untypedTupleSelectedType_recursionNeutral (arity : Nat) :
    SelectedApplicationRecursionNeutral (untypedTupleSelectedType arity) arity := by
  constructor
  · rw [argumentEvaluationPolicies_untypedTuple]
    intro policy hpolicy _
    have hEq : policy = (true, Atom.sym "%Undefined%") :=
      (List.mem_replicate.mp hpolicy).2
    simp [hEq]
  · intro _
    exact selectedResultExpected_untypedTuple arity

def RecursionNeutralApplicationPolicy.ofSelected
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env world (.sym op) args = .selected selected)
    (planCorresponds : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hneutral : SelectedApplicationRecursionNeutral selected args.length) :
    RecursionNeutralApplicationPolicy env world op args
      (argMask selected args.length) (returnsAtom selected) :=
  ⟨.selected selected hSelected, planCorresponds, hneutral, rfl, rfl⟩

def RecursionNeutralApplicationPolicy.ofUntypedTuple
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true)
    (planCorresponds : ApplicationPlanCorresponds [] (.untypedTuple hScan)) :
    RecursionNeutralApplicationPolicy env world op args
      (List.replicate args.length true) false :=
  ⟨.untypedTuple hScan, planCorresponds,
    untypedTupleSelectedType_recursionNeutral args.length,
    argMask_untypedTuple args.length, returnsAtom_untypedTuple args.length⟩

def RecursionNeutralApplicationPolicy.selected
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env world (.sym op) args = .selected selected)
    (planCorresponds : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hneutral : SelectedApplicationRecursionNeutral selected args.length) :
    RecursionNeutralApplicationPolicy env world op args
      (argMask selected args.length) (returnsAtom selected) :=
  .ofSelected selected hSelected planCorresponds hneutral

def RecursionNeutralApplicationPolicy.untypedTuple
    {env : MinEnv} {world : World} {op : String} {args : List Atom}
    (hScan : selectFunctionType env world (.sym op) args = .exhausted [] true)
    (planCorresponds : ApplicationPlanCorresponds [] (.untypedTuple hScan)) :
    RecursionNeutralApplicationPolicy env world op args
      (List.replicate args.length true) false :=
  .ofUntypedTuple hScan planCorresponds

/-- Compatibility boundary for recursion-neutral selected policies.  The runtime decision remains
data-bearing; the Boolean mask and return flag on the right are derived from that decision. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactDecision
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (policy : ExactApplicationPolicy env st.world op args)
    (planCorresponds : ApplicationPlanCorresponds [] policy)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hneutral : SelectedApplicationRecursionNeutral policy.selectedType args.length) :
    mettaEval env (fuel + 1) st [] (Atom.expr (Atom.sym op :: args)) =
      prioritizeSemanticResults (evaluateSelectedApplication
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := [] }] [])
        st op args policy.argumentMask policy.returnIsAtom) := by
  cases policy with
  | selected selected hSelected =>
      rw [mettaEval_eq_evaluateExpectedApplication_of_selected
        env fuel st op args selected hNotError hSelected planCorresponds]
      congr 1
      exact evaluateExpectedApplication_eq_evaluateSelectedApplication_of_recursionNeutral
        _ _ _ st op args selected hneutral
          (mettaEvalExpected_undefined env fuel)
  | untypedTuple hScan =>
      simpa [ExactApplicationPolicy.argumentMask, ExactApplicationPolicy.returnIsAtom,
        ExactApplicationPolicy.selectedType] using
        mettaEval_eq_evaluateSelectedApplication_of_untypedTuple
          env fuel st op args hNotError hScan planCorresponds

/-- Incoming-binding sibling of
`mettaEval_eq_evaluateSelectedApplication_of_exactPolicy`. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactDecision_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (policy : ExactApplicationPolicy env st.world op args)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (hSelectedType : plan.selected = policy.selectedTypeFrom bnd)
    (hSeed : plan.seeds = [bnd])
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (_hneutral : SelectedApplicationRecursionNeutral policy.selectedType args.length) :
    mettaEval env (fuel + 1) st bnd source =
      prioritizeSemanticResults (evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bnd }] [])
        bnd st op args (policy.selectedTypeFrom bnd)) := by
  rw [← hSelectedType]
  exact mettaEval_eq_evaluateExpectedApplication_of_selected_after_instantiate
    env fuel st bnd source op args hInstantiate hNotError plan hSeed

/-- Boolean-view compatibility corollary of the data-bearing decision boundary. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st : St) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool)
    (policy : RecursionNeutralApplicationPolicy
      env st.world op args mask returnAtom)
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false) :
    mettaEval env (fuel + 1) st [] (Atom.expr (Atom.sym op :: args)) =
      prioritizeSemanticResults (evaluateSelectedApplication
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := [] }] [])
        st op args mask returnAtom) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactDecision
    env fuel st op args policy.decision policy.planCorresponds hNotError
      policy.recursionNeutral]
  rw [policy.argumentMask_eq, policy.returnIsAtom_eq]

/-- A non-error result of the quoted/evaluated/quoted worker rules out an
early stop at the first quoted slot.  This is weaker than requiring the quoted
atom itself not to be an error: a reflexive error atom is harmless, while a
changed reflexive comparison is exactly what the worker propagates. -/
theorem evaluateSelectedApplicationFactored_first_quoted_not_changed_of_mem
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (p atom templ : Atom)
    (result : Atom × Bindings)
    (hResultNotError : result.1.isError = false)
    (hmem : result ∈
      (evaluateSelectedApplicationFactored evalRecursive reduceApplication
        st op [p, atom, templ] [false, true, false] false).1) :
    ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) := by
  intro hChanged
  have hresult : result = (p, []) := by
    simpa [evaluateSelectedApplicationFactored, selectedArgumentFoldStep,
      selectedResultFoldStep, Metta.instantiate_nil, hChanged] using hmem
  have hpNotError : p.isError = false := by
    rw [hresult] at hResultNotError
    exact hResultNotError
  rcases hChanged.1 with hEmpty | hError
  · have hp : p = emptyA := (beq_empty_eq_true_iff p).mp hEmpty
    subst p
    exact Bool.noConfusion (hChanged.2.symm.trans (by rfl))
  · exact Bool.noConfusion (hpNotError.symm.trans hError)

/-- `mettaEval` exposes the same first-slot chronology boundary after exact
policy selection and semantic-result prioritization. -/
theorem mettaEval_quoted_eval_quoted_first_not_changed_of_mem
    (env : MinEnv) (fuel : Nat) (st : St) (op : String)
    (p atom templ : Atom) (result : Atom × Bindings)
    (hResultNotError : result.1.isError = false)
    (policy : RecursionNeutralApplicationPolicy env st.world op
      [p, atom, templ] [false, true, false] false)
    (hNotError :
      (Atom.expr [Atom.sym op, p, atom, templ]).isError = false)
    (hmem : result ∈
      (mettaEval env (fuel + 1) st []
        (Atom.expr [Atom.sym op, p, atom, templ])).1) :
    ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [p, atom, templ] [false, true, false] false
      policy hNotError] at hmem
  have hworker := mem_of_mem_prioritizeSemanticResults hmem
  rw [evaluateSelectedApplication_eq_factored] at hworker
  exact
    evaluateSelectedApplicationFactored_first_quoted_not_changed_of_mem
      (mettaEval env fuel)
      (fun nextSt application =>
        interpretFuel env (fuel + 1) nextSt
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval", application]) [], bnd := [] }] [])
      st op p atom templ result hResultNotError hworker

/-- The first quoted slot of one live quoted/evaluated/quoted application did
not trigger the changed-terminal guard whenever a retained result is neither
an error nor `Empty`.  The compared value is the quoted atom instantiated by
the actual applicability-produced seed; no coincidence with empty bindings is
assumed. -/
theorem evaluateExpectedApplicationFrom_quoted_eval_quoted_first_not_changed_of_mem
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st : St) (op : String)
    (p atom templ : Atom) (selected : SelectedFunctionType)
    (result : Atom × Bindings)
    (hPolicies :
      argumentEvaluationPolicies selected 3 =
        [(false, .sym "Atom"), (true, .sym "%Undefined%"),
          (false, .sym "Atom")])
    (hResultNotError : result.1.isError = false)
    (hResultNotEmpty : result.1 ≠ emptyA)
    (hmem : result ∈
      (evaluateExpectedApplicationFrom evalRecursive reduceApplication
        initialBindings st op [p, atom, templ] selected).1) :
    let pOut := instantiate initialBindings p
    ¬ (((pOut == emptyA) = true ∨ pOut.isError = true) ∧
      (pOut != p) = true) := by
  dsimp only
  intro hChanged
  let pOut := instantiate initialBindings p
  have hArgs :
      expectedApplicationArgumentFold evalRecursive initialBindings st
          [p, atom, templ] selected =
        ([([pOut], initialBindings)], st) := by
    unfold expectedApplicationArgumentFold
    simp only [List.length_cons, List.length_nil]
    rw [hPolicies]
    simp [expectedArgumentFoldStep, pOut, hChanged]
  rw [evaluateExpectedApplicationFrom_eq_factored] at hmem
  rw [evaluateExpectedApplicationFromFactored_eq_resultFold_of_argumentFold
    evalRecursive reduceApplication initialBindings st st op
      [p, atom, templ] selected [([pOut], initialBindings)] hArgs] at hmem
  have hresult : result = (pOut, initialBindings) := by
    simpa [expectedApplicationResultFold, expectedResultFoldStep,
      pOut, hChanged] using hmem
  have hpOutNotError : pOut.isError = false := by
    rw [hresult] at hResultNotError
    exact hResultNotError
  have hpOutNotEmpty : pOut ≠ emptyA := by
    rw [hresult] at hResultNotEmpty
    exact hResultNotEmpty
  rcases hChanged.1 with hEmpty | hError
  · exact hpOutNotEmpty ((beq_empty_eq_true_iff pOut).mp hEmpty)
  · exact Bool.noConfusion (hpOutNotError.symm.trans hError)

/-- The quoted/evaluated/quoted argument worker is an ordered completion of
the middle argument's readouts.  The exact boundary is that the first quoted
slot did not trigger the changed-error guard; the atom may itself be an error
when its reflexive comparison is stable. -/
theorem selectedArgumentFold_quoted_eval_quoted_eq_completed
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (st stArg : St) (p atom templ : Atom)
    (argPairs : List (Atom × Bindings))
    (hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true))
    (hArg : evalRecursive st [] atom = (argPairs, stArg)) :
    let source := [p, atom, templ]
    let queryVars := source.flatMap Atom.vars
    let rows := argPairs.map (fun out : Atom × Bindings =>
      ([p, out.1],
        restrictBnd queryVars
          ((Bindings.merge [] out.2).head?.getD out.2)))
    let parts := rows.map (completeQuotedTailArgument source templ)
    (source.zip [false, true, false]).foldl
        (selectedArgumentFoldStep evalRecursive queryVars source)
        ([([], [])], st) =
      (parts, stArg) := by
  dsimp only
  let source := [p, atom, templ]
  let queryVars := source.flatMap Atom.vars
  let rows : List (List Atom × Bindings) :=
    argPairs.map (fun out : Atom × Bindings =>
      ([p, out.1],
        restrictBnd queryVars
          ((Bindings.merge [] out.2).head?.getD out.2)))
  let parts := rows.map (completeQuotedTailArgument source templ)
  simp only [List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  unfold selectedArgumentFoldStep
  simp [Metta.instantiate_nil, hPNotChanged]
  rw [hArg]
  simpa [rows, parts, source, queryVars] using
    (foldl_completeQuotedTailArgument source templ stArg [] rows)

/-- Live-binding form of the quoted/evaluated/quoted argument worker.  The
incoming theory is used for the first quoted atom and for the evaluated
middle atom; every middle readout is merged back into that theory before the
quoted tail is instantiated.  No equality with empty-binding evaluation is
claimed. -/
theorem expectedApplicationArgumentFold_quoted_eval_quoted_eq_completed
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (initialBindings : Bindings) (st stArg : St)
    (p atom templ : Atom) (selected : SelectedFunctionType)
    (argPairs : List (Atom × Bindings))
    (hPolicies :
      argumentEvaluationPolicies selected 3 =
        [(false, .sym "Atom"), (true, .sym "%Undefined%"),
          (false, .sym "Atom")])
    (hPNotChanged :
      let pOut := instantiate initialBindings p
      ¬ (((pOut == emptyA) = true ∨ pOut.isError = true) ∧
        (pOut != p) = true))
    (hArg :
      evalRecursive st initialBindings atom (.sym "%Undefined%") =
        (argPairs, stArg)) :
    let source := [p, atom, templ]
    let pOut := instantiate initialBindings p
    let queryVars := expectedApplicationRetentionScope initialBindings source
    let rows := argPairs.map (fun out : Atom × Bindings =>
      ([pOut, out.1],
        restrictBnd queryVars
          ((Bindings.merge initialBindings out.2).head?.getD out.2)))
    let parts := rows.map (completeQuotedTailArgument source templ)
    expectedApplicationArgumentFold evalRecursive initialBindings st source selected =
      (parts, stArg) := by
  dsimp only
  let source := [p, atom, templ]
  let pOut := instantiate initialBindings p
  let queryVars := expectedApplicationRetentionScope initialBindings source
  let rows : List (List Atom × Bindings) :=
    argPairs.map (fun out : Atom × Bindings =>
      ([pOut, out.1],
        restrictBnd queryVars
          ((Bindings.merge initialBindings out.2).head?.getD out.2)))
  let parts := rows.map (completeQuotedTailArgument source templ)
  unfold expectedApplicationArgumentFold
  simp only [List.length_cons, List.length_nil]
  rw [hPolicies]
  simp only [List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  unfold expectedArgumentFoldStep
  simp [hPNotChanged]
  rw [hArg]
  simpa [rows, parts, source, queryVars] using
    (foldl_completeQuotedTailArgument source templ stArg [] rows)

/-- Decompose one concrete quoted/evaluated/quoted selected worker without
forgetting its live seed or branch-entry state.  This is the common worker
brick used by both plain membership extraction and invariant-aware ordered
seed traversal. -/
theorem evaluateExpectedApplicationFrom_quoted_eval_quoted_mem_implies_partFold
    (env : MinEnv) (fuel : Nat) (seed : Bindings) (branchState : St)
    (op : String) (p atom templ : Atom) (selected : SelectedFunctionType)
    (result : Atom × Bindings)
    (hPolicies :
      argumentEvaluationPolicies selected 3 =
        [(false, .sym "Atom"), (true, .sym "%Undefined%"),
          (false, .sym "Atom")])
    (hReturn : returnsAtom selected = false)
    (hResultExpected :
      selectedResultExpected selected = .sym "%Undefined%")
    (hResultNotError : result.1.isError = false)
    (hResultNotEmpty : result.1 ≠ emptyA)
    (hWorker : result ∈
      (evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
        seed branchState op [p, atom, templ] selected).1) :
    ∃ argPairs stArg,
      mettaEval env fuel branchState seed atom = (argPairs, stArg) ∧
      let sourceArgs := [p, atom, templ]
      let pOut := instantiate seed p
      let queryVars := expectedApplicationRetentionScope seed sourceArgs
      let rows := argPairs.map (fun out : Atom × Bindings =>
        ([pOut, out.1],
          restrictBnd queryVars
            ((Bindings.merge seed out.2).head?.getD out.2)))
      let parts := rows.map (completeQuotedTailArgument sourceArgs templ)
      result ∈
        (parts.foldl
          (mettaEvalExprPartFoldStep env fuel queryVars op sourceArgs seed false)
          ([], stArg)).1 := by
  have hPNotChanged :
      let pOut := instantiate seed p
      ¬ (((pOut == emptyA) = true ∨ pOut.isError = true) ∧
        (pOut != p) = true) :=
    evaluateExpectedApplicationFrom_quoted_eval_quoted_first_not_changed_of_mem
      (fun nextSt nextBindings nextAtom nextExpected =>
        mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
      (fun nextSt application =>
        interpretFuel env (fuel + 1) nextSt
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
      seed branchState op p atom templ selected result hPolicies
      hResultNotError hResultNotEmpty hWorker
  cases hArg : mettaEval env fuel branchState seed atom with
  | mk argPairs stArg =>
      have hArgExpected :
          mettaEvalExpected env fuel branchState seed atom
              (.sym "%Undefined%") =
            (argPairs, stArg) := by
        rw [mettaEvalExpected_undefined]
        exact hArg
      let sourceArgs := [p, atom, templ]
      let pOut := instantiate seed p
      let queryVars := expectedApplicationRetentionScope seed sourceArgs
      let rows : List (List Atom × Bindings) :=
        argPairs.map (fun out : Atom × Bindings =>
          ([pOut, out.1],
            restrictBnd queryVars
              ((Bindings.merge seed out.2).head?.getD out.2)))
      let parts := rows.map (completeQuotedTailArgument sourceArgs templ)
      have hPartials :
          expectedApplicationArgumentFold
              (fun nextSt nextBindings nextAtom nextExpected =>
                mettaEvalExpected env fuel nextSt nextBindings nextAtom
                  nextExpected)
              seed branchState sourceArgs selected =
            (parts, stArg) := by
        simpa [sourceArgs, pOut, queryVars, rows, parts] using
          (expectedApplicationArgumentFold_quoted_eval_quoted_eq_completed
            (fun nextSt nextBindings nextAtom nextExpected =>
              mettaEvalExpected env fuel nextSt nextBindings nextAtom
                nextExpected)
            seed branchState stArg p atom templ selected argPairs
            hPolicies hPNotChanged hArgExpected)
      have hWorkerFactored := hWorker
      rw [evaluateExpectedApplicationFrom_eq_factored] at hWorkerFactored
      rw [evaluateExpectedApplicationFromFactored_eq_selectedResultFold_of_argumentFold
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt nextBindings nextAtom =>
          mettaEval env fuel nextSt nextBindings nextAtom)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
        seed branchState stArg op sourceArgs selected parts hPartials
        (fun _ => hResultExpected) (mettaEvalExpected_undefined env fuel)]
        at hWorkerFactored
      rw [hReturn] at hWorkerFactored
      rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep
        env fuel queryVars op sourceArgs seed false] at hWorkerFactored
      exact ⟨argPairs, stArg, rfl, by
        simpa [sourceArgs, pOut, queryVars, rows, parts] using hWorkerFactored⟩

/-- Exact live replacement for the legacy quoted/evaluated/quoted
after-instantiation helper.  The witness retains the applicability-produced
seed and the chronology-local state at which that seed's branch begins; the
middle argument is evaluated under that seed, and the same seed is used by
the result worker. -/
theorem mettaEval_quoted_eval_quoted_mem_implies_live_partFold_mem_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (incoming : Bindings)
    (source : Atom) (op : String) (p atom templ : Atom)
    (plan : SelectedApplicationExecutionPlan env st.world incoming op
      [p, atom, templ])
    (result : Atom × Bindings)
    (hInstantiate : instantiate incoming source =
      Atom.expr [Atom.sym op, p, atom, templ])
    (hApplicationNotError :
      (Atom.expr [Atom.sym op, p, atom, templ]).isError = false)
    (hPolicies :
      argumentEvaluationPolicies plan.selected 3 =
        [(false, .sym "Atom"), (true, .sym "%Undefined%"),
          (false, .sym "Atom")])
    (hReturn : returnsAtom plan.selected = false)
    (hResultExpected :
      selectedResultExpected plan.selected = .sym "%Undefined%")
    (hResultNotError : result.1.isError = false)
    (hResultNotEmpty : result.1 ≠ emptyA)
    (hmem : result ∈ (mettaEval env (fuel + 1) st incoming source).1) :
    ∃ seed ∈ plan.seeds, ∃ branchState argPairs stArg,
      mettaEval env fuel branchState seed atom = (argPairs, stArg) ∧
      let sourceArgs := [p, atom, templ]
      let pOut := instantiate seed p
      let queryVars := expectedApplicationRetentionScope seed sourceArgs
      let rows := argPairs.map (fun out : Atom × Bindings =>
        ([pOut, out.1],
          restrictBnd queryVars
            ((Bindings.merge seed out.2).head?.getD out.2)))
      let parts := rows.map (completeQuotedTailArgument sourceArgs templ)
      result ∈
        (parts.foldl
          (mettaEvalExprPartFoldStep env fuel queryVars op sourceArgs seed false)
          ([], stArg)).1 := by
  rcases
      mettaEval_mem_implies_evaluateExpectedApplicationFrom_of_selected_after_instantiate
        env fuel st incoming source op [p, atom, templ]
        hInstantiate hApplicationNotError plan result hmem with
    ⟨seed, hSeed, branchState, hWorker⟩
  rcases
      evaluateExpectedApplicationFrom_quoted_eval_quoted_mem_implies_partFold
        env fuel seed branchState op p atom templ plan.selected result
        hPolicies hReturn hResultExpected hResultNotError hResultNotEmpty hWorker with
    ⟨argPairs, stArg, hArg, hPartFold⟩
  exact ⟨seed, hSeed, branchState, argPairs, stArg, hArg, hPartFold⟩

/-- Invariant-aware live quoted/evaluated/quoted extraction.  The predicate
is certified at the actual branch-entry state reached after all earlier
applicability seeds; it is never transported from an independent copy of the
initial state. -/
theorem mettaEval_quoted_eval_quoted_mem_implies_live_partFold_mem_after_instantiate_of_invariant
    (env : MinEnv) (fuel : Nat) (st : St) (incoming : Bindings)
    (source : Atom) (op : String) (p atom templ : Atom)
    (plan : SelectedApplicationExecutionPlan env st.world incoming op
      [p, atom, templ])
    (result : Atom × Bindings) (P : St → Prop)
    (hInitial : P st)
    (hStep : ∀ branchState seed,
      P branchState →
        P (evaluateExpectedApplicationFrom
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          (fun nextSt application =>
            interpretFuel env (fuel + 1) nextSt
              [{ stack := atomToStack
                  (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
          seed branchState op [p, atom, templ] plan.selected).2)
    (hInstantiate : instantiate incoming source =
      Atom.expr [Atom.sym op, p, atom, templ])
    (hApplicationNotError :
      (Atom.expr [Atom.sym op, p, atom, templ]).isError = false)
    (hPolicies :
      argumentEvaluationPolicies plan.selected 3 =
        [(false, .sym "Atom"), (true, .sym "%Undefined%"),
          (false, .sym "Atom")])
    (hReturn : returnsAtom plan.selected = false)
    (hResultExpected :
      selectedResultExpected plan.selected = .sym "%Undefined%")
    (hResultNotError : result.1.isError = false)
    (hResultNotEmpty : result.1 ≠ emptyA)
    (hmem : result ∈ (mettaEval env (fuel + 1) st incoming source).1) :
    ∃ seed ∈ plan.seeds, ∃ branchState argPairs stArg,
      P branchState ∧
      mettaEval env fuel branchState seed atom = (argPairs, stArg) ∧
      let sourceArgs := [p, atom, templ]
      let pOut := instantiate seed p
      let queryVars := expectedApplicationRetentionScope seed sourceArgs
      let rows := argPairs.map (fun out : Atom × Bindings =>
        ([pOut, out.1],
          restrictBnd queryVars
            ((Bindings.merge seed out.2).head?.getD out.2)))
      let parts := rows.map (completeQuotedTailArgument sourceArgs templ)
      result ∈
        (parts.foldl
          (mettaEvalExprPartFoldStep env fuel queryVars op sourceArgs seed false)
          ([], stArg)).1 := by
  rw [mettaEval_eq_evaluateExpectedApplicationSeeds_of_selected_after_instantiate
    env fuel st incoming source op [p, atom, templ]
    hInstantiate hApplicationNotError plan] at hmem
  have hmemRaw := mem_of_mem_prioritizeSemanticResults hmem
  rcases
      mem_evaluateExpectedApplicationSeeds_of_invariant
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun seed nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := seed }] [])
        plan.seeds st op [p, atom, templ] plan.selected result P
        hInitial hStep hmemRaw with
    ⟨seed, hSeed, branchState, hPBranch, hWorker⟩
  rcases
      evaluateExpectedApplicationFrom_quoted_eval_quoted_mem_implies_partFold
        env fuel seed branchState op p atom templ plan.selected result
        hPolicies hReturn hResultExpected hResultNotError hResultNotEmpty hWorker with
    ⟨argPairs, stArg, hArg, hPartFold⟩
  exact
    ⟨seed, hSeed, branchState, argPairs, stArg, hPBranch, hArg, hPartFold⟩

/-- Exact factored-worker boundary for one quoted/evaluated/quoted row.

The evaluated middle argument returns one empty-binding readout, while the
full changed-error guard certifies that the two quoted slots and that readout
reach the root worker as one completed row.  The statement retains the actual
ordered argument fold and therefore does not assume lawful `BEq` for quoted
atoms. -/
theorem evaluateSelectedApplicationFactored_quoted_eval_quoted_singleton_eq_partFoldStep
    (env : MinEnv) (fuel : Nat) (st stArg : St) (op : String)
    (p atom templ atomOut : Atom)
    (hArg : mettaEval env fuel st [] atom = ([(atomOut, [])], stArg))
    (hNoError :
      (([p, atomOut, templ].zip [p, atom, templ]).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none) :
    evaluateSelectedApplicationFactored
        (mettaEval env fuel)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := [] }] [])
        st op [p, atom, templ] [false, true, false] false =
      mettaEvalExprPartFoldStep env fuel
        ([p, atom, templ].flatMap Atom.vars) op [p, atom, templ]
        [] false ([], stArg) ([p, atomOut, templ], []) := by
  let source := [p, atom, templ]
  let queryVars := source.flatMap Atom.vars
  have hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := p) (original := p) hNoError (by simp)
  have hPrefix :
      (([p, atomOut].zip source).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none :=
    changedArgumentStop_prefix_none [p, atomOut] [templ] source
      (by simpa [source] using hNoError)
  have hPrefixConcrete :
      (([p, atomOut].zip [p, atom, templ]).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none := by
    simpa [source] using hPrefix
  have hPrefixList :
      List.find? (fun pair : Atom × Atom =>
        (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)
        [(p, p), (atomOut, atom)] = none := by
    simpa using hPrefixConcrete
  have hpartials :
      (source.zip [false, true, false]).foldl
          (selectedArgumentFoldStep (mettaEval env fuel) queryVars source)
          ([([], [])], st) =
        ([([p, atomOut, templ], [])], stArg) := by
    have hcompleted :=
      selectedArgumentFold_quoted_eval_quoted_eq_completed
        (mettaEval env fuel) st stArg p atom templ [(atomOut, [])]
        hPNotChanged hArg
    simpa [source, queryVars, completeQuotedTailArgument,
      restrictBnd_empty_merge_empty, hPrefixList,
      Metta.instantiate_nil] using hcompleted
  have hpartialsConcrete :
      ([p, atom, templ].zip [false, true, false]).foldl
          (selectedArgumentFoldStep (mettaEval env fuel)
            ([p, atom, templ].flatMap Atom.vars) [p, atom, templ])
          ([([], [])], st) =
        ([([p, atomOut, templ], [])], stArg) := by
    simpa [source, queryVars] using hpartials
  simp only [evaluateSelectedApplicationFactored]
  rw [hpartialsConcrete]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]
  rfl

/-- A successful readout of a quoted/evaluated/quoted application belongs to
the ordered result fold over the worker's completed partial rows.  A non-error
readout itself proves that the first quoted slot did not stop the worker. -/
theorem mettaEval_quoted_eval_quoted_mem_implies_partFold_mem
    (env : MinEnv) (fuel : Nat) (st stArg : St) (op : String)
    (p atom templ : Atom) (argPairs : List (Atom × Bindings))
    (result : Atom × Bindings)
    (hResultNotError : result.1.isError = false)
    (hArg : mettaEval env fuel st [] atom = (argPairs, stArg))
    (policy : RecursionNeutralApplicationPolicy env st.world op
      [p, atom, templ] [false, true, false] false)
    (hNotError :
      (Atom.expr [Atom.sym op, p, atom, templ]).isError = false)
    (hmem : result ∈
      (mettaEval env (fuel + 1) st []
        (Atom.expr [Atom.sym op, p, atom, templ])).1) :
    let source := [p, atom, templ]
    let queryVars := source.flatMap Atom.vars
    let rows := argPairs.map (fun out : Atom × Bindings =>
      ([p, out.1],
        restrictBnd queryVars
          ((Bindings.merge [] out.2).head?.getD out.2)))
    let parts := rows.map (completeQuotedTailArgument source templ)
    result ∈
      (parts.foldl
        (mettaEvalExprPartFoldStep env fuel queryVars op source [] false)
        ([], stArg)).1 := by
  dsimp only
  let source := [p, atom, templ]
  let queryVars := source.flatMap Atom.vars
  let rows : List (List Atom × Bindings) :=
    argPairs.map (fun out : Atom × Bindings =>
      ([p, out.1],
        restrictBnd queryVars
          ((Bindings.merge [] out.2).head?.getD out.2)))
  let parts := rows.map (completeQuotedTailArgument source templ)
  have hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) :=
    mettaEval_quoted_eval_quoted_first_not_changed_of_mem
      env fuel st op p atom templ result hResultNotError policy hNotError hmem
  have hpartials :
      (source.zip [false, true, false]).foldl
          (selectedArgumentFoldStep (mettaEval env fuel) queryVars source)
          ([([], [])], st) =
        (parts, stArg) := by
    simpa [source, queryVars, rows, parts] using
      (selectedArgumentFold_quoted_eval_quoted_eq_completed
        (mettaEval env fuel) st stArg p atom templ argPairs hPNotChanged hArg)
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op source [false, true, false] false policy hNotError] at hmem
  have hworker := mem_of_mem_prioritizeSemanticResults hmem
  rw [evaluateSelectedApplication_eq_factored] at hworker
  simp only [evaluateSelectedApplicationFactored] at hworker
  rw [hpartials] at hworker
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep
    env fuel queryVars op source [] false] at hworker
  simpa [source, queryVars, rows, parts] using hworker

/-- Incoming-binding sibling of the checked Boolean-view compatibility boundary. -/
theorem mettaEval_eq_evaluateSelectedApplication_of_exactPolicy_after_instantiate
    (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (source : Atom)
    (op : String) (args : List Atom) (mask : List Bool) (returnAtom : Bool)
    (hInstantiate : instantiate bnd source = Atom.expr (Atom.sym op :: args))
    (policy : RecursionNeutralApplicationPolicy
      env st.world op args mask returnAtom)
    (plan : SelectedApplicationExecutionPlan env st.world bnd op args)
    (hSelectedType : plan.selected = policy.decision.selectedTypeFrom bnd)
    (hSeed : plan.seeds = [bnd])
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false) :
    mettaEval env (fuel + 1) st bnd source =
      prioritizeSemanticResults (evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bnd }] [])
        bnd st op args (policy.decision.selectedTypeFrom bnd)) := by
  exact mettaEval_eq_evaluateSelectedApplication_of_exactDecision_after_instantiate
    env fuel st bnd source op args hInstantiate policy.decision
      plan hSelectedType hSeed hNotError policy.recursionNeutral

/-- One-argument constructor congruence for the executable `mettaEval` loop.

If the single argument of `(op arg)` evaluates to one readout `out`, and the rebuilt root
`(op out)` reports `NotReducible`, then the full evaluator keeps `(op out)`. This is the generic
outer-loop lemma needed by Peano-style constructors before proving a full evaluator computation
theorem; it avoids tracing one constructor layer at a time. -/
theorem mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : (out == emptyA || out.isError) = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := by simp [Atom.isError, hOpNotError])
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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
    (hroot : (notReducibleA, []) ∈
      (interpretFuel env (fuel + 1) stArg
        [evalItemNil (Atom.expr [Atom.sym op, out])] []).1) :
    (Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  exact mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    env fuel st stArg op hOpNotError arg out (argMask selected 1) (returnsAtom selected)
    hArg (.selected selected hSelected hPlan hNeutral) hMask hNotError hroot

/-- Membership-side soundness package for the unary constructor fold.

This is the non-exact counterpart of
`mettaEval_unary_expr_singleton_sound_of_arg_singleton_and_notReducible_eq`: it keeps the root
minimal-interpreter result as a membership premise and returns the actual outer readout together
with the caller-supplied certified relation chain under the constructor. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
        env fuel st stArg op hOpNotError arg out mask returnAtom hArg hPolicy hMask hNotError hroot
  · exact hReach

/-- Selected-signature specialization of the unary singleton relation package. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
    env fuel st stArg op hOpNotError arg out (argMask selected 1) (returnsAtom selected) R
    hArg (.selected selected hSelected hPlan hNeutral) hMask hNotError hroot hReach

/-- Unary constructor readout from a selected argument readout.

Unlike the singleton package above, this theorem allows the argument evaluator to return many
readouts.  The selected readout is followed through the argument-fold into the root-fold.  The root
`NotReducible` premise is quantified over every threaded state because earlier partials in the same
fold may have advanced the evaluator state before the selected partial is processed. -/
theorem mettaEval_unary_expr_keeps_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
  have hnoerr : (part.1.zip [arg]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none := by
    simp [part, hNotError]
  have hrootPart :
      ∀ acc : List (Atom × Bindings) × St,
        (notReducibleA, []) ∈
          (interpretFuel env (fuel + 1) acc.2
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr (Atom.sym op :: part.1)]) [], bnd := [] }] []).1 := by
    intro acc
    simpa [part, evalItemNil] using hroot acc.2
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] (argMask selected 1) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp [evaluateSelectedApplication, hMask]
  rw [hArg]
  simp
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := by simp [Atom.isError, hOpNotError])
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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (mask : List Bool) (returnAtom : Bool)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
  have hnoerr : (part.1.zip [arg]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none := by
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
    env fuel st op [arg] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
  simp [evaluateSelectedApplication, hMask]
  rw [hArg]
  simp
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := by simp [Atom.isError, hOpNotError])
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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
    env fuel st stArg op hOpNotError arg out argPairs (argMask selected 1) (returnsAtom selected) P
    hArg hmemArg (.selected selected hSelected hPlan hNeutral) hMask hNotError hinit hstep hroot

/-- Relation-sound package for the selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_all_states
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
        env fuel st stArg op hOpNotError arg out argPairs selected hArg hmemArg hSelected hPlan
        hNeutral hMask
        hNotError hroot
  · exact hReach

/-- Relation-sound package for the invariant-aware selected-readout unary constructor theorem. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (mask : List Bool) (returnAtom : Bool)
    (P : St → Prop) (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
        env fuel st stArg op hOpNotError arg out argPairs mask returnAtom P hArg hmemArg hPolicy hMask
        hNotError hinit hstep hroot
  · exact hReach

/-- Selected-signature specialization of the invariant-aware unary relation package. -/
theorem mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred
    (env : MinEnv) (fuel : Nat) (st stArg : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (argPairs : List (Atom × Bindings))
    (selected : SelectedFunctionType)
    (P : St → Prop) (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
    env fuel st stArg op hOpNotError arg out argPairs (argMask selected 1) (returnsAtom selected) P R
    hArg hmemArg (.selected selected hSelected hPlan hNeutral) hMask hNotError hinit hstep hroot hReach

/-- Exact one-argument constructor congruence for the executable `mettaEval` loop.

This is still a one-layer theorem: callers provide the argument evaluator result and the rebuilt
root evaluator result. It is useful for inductive proofs, but it does not encode any concrete Peano
fuel arithmetic. -/
theorem evaluateExpectedApplicationFrom_unary_eq_of_argumentFold_and_notReducible
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (bnd : Bindings) (op : String) (arg' out : Atom)
    (partBnd rootBnd : Bindings) (selected : SelectedFunctionType)
    (returnAtom : Bool)
    (hArguments :
      expectedApplicationArgumentFold
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          bnd st [arg'] selected =
        ([([out], partBnd)], stArg))
    (hResultExpected :
      returnsAtom selected = false →
        selectedResultExpected selected = Atom.sym "%Undefined%")
    (hReturn : returnsAtom selected = returnAtom)
    (hNoChanged :
      (([out].zip [arg']).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot :
      interpretFuel env (fuel + 1) stArg
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [],
             bnd := bnd }] [] =
        ([(notReducibleA, rootBnd)], stRoot)) :
    evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        bnd st op [arg'] selected =
      ([(Atom.expr [Atom.sym op, out], partBnd)], stRoot) := by
  rw [evaluateExpectedApplicationFrom_eq_factored]
  rw [evaluateExpectedApplicationFromFactored_eq_selectedResultFold_of_argumentFold
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    (fun nextSt nextBindings nextAtom =>
      mettaEval env fuel nextSt nextBindings nextAtom)
    (fun nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
    bnd st stArg op [arg'] selected
    [([out], partBnd)] hArguments hResultExpected
    (mettaEvalExpected_undefined env fuel)]
  rw [hReturn]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]
  unfold mettaEvalExprPartFoldStep
  rw [hNoChanged]
  simp only [List.nil_append]
  rw [hRoot]
  rw [mettaEvalExprRootFold_eq_of_notReducible_singleton]

theorem mettaEval_unary_expr_eq_of_instantiated_argumentFold_and_notReducible_from
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (bnd : Bindings) (op : String) (hOpNotError : op ≠ "Error")
    (arg arg' out : Atom) (partBnd rootBnd : Bindings)
    (returnAtom : Bool)
    (hInst :
      instantiate bnd (Atom.expr [Atom.sym op, arg]) =
        Atom.expr [Atom.sym op, arg'])
    (hPlan : RecursionNeutralApplicationExecutionPlan
      env st.world bnd op [arg'] [true] returnAtom)
    (hArguments :
      expectedApplicationArgumentFold
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          bnd st [arg'] hPlan.plan.selected =
        ([([out], partBnd)], stArg))
    (hNoChanged :
      (([out].zip [arg']).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot :
      interpretFuel env (fuel + 1) stArg
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [],
             bnd := bnd }] [] =
        ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st bnd (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out], partBnd)], stRoot) := by
  rw [mettaEval_eq_evaluateExpectedApplication_of_selected_after_instantiate
    env fuel st bnd (Atom.expr [Atom.sym op, arg]) op [arg'] hInst
      (by simp [Atom.isError, hOpNotError]) hPlan.plan hPlan.seedSingleton]
  rw [evaluateExpectedApplicationFrom_unary_eq_of_argumentFold_and_notReducible
    env fuel st stArg stRoot bnd op arg' out partBnd rootBnd hPlan.plan.selected
      returnAtom hArguments hPlan.recursionNeutral.resultExpected
      hPlan.returnIsAtom_eq hNoChanged hRoot]
  simp

/-- Tuple-fallback entry specialization of the live unary constructor theorem.

The tuple payload carries `bnd` as its type theory, but its argument and result policies remain
ordinary evaluation under `%Undefined%`.  The inner argument/root calculation is shared with the
selected-signature theorem above. -/
theorem mettaEval_unary_expr_eq_of_untypedTuple_argumentFold_and_notReducible_from
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (bnd : Bindings) (op : String) (hOpNotError : op ≠ "Error")
    (arg arg' out : Atom) (partBnd rootBnd : Bindings)
    (hInst :
      instantiate bnd (Atom.expr [Atom.sym op, arg]) =
        Atom.expr [Atom.sym op, arg'])
    (hScan :
      selectFunctionType env st.world (.sym op) [arg'] = .exhausted [] true)
    (hPlan : ApplicationPlanCorresponds bnd (.untypedTuple hScan))
    (hArguments :
      expectedApplicationArgumentFold
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          bnd st [arg'] (untypedTupleSelectedTypeFrom bnd 1) =
        ([([out], partBnd)], stArg))
    (hNoChanged :
      (([out].zip [arg']).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot :
      interpretFuel env (fuel + 1) stArg
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [],
             bnd := bnd }] [] =
        ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st bnd (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out], partBnd)], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_untypedTuple_after_instantiate
    env fuel st bnd (Atom.expr [Atom.sym op, arg]) op [arg'] hInst
      (by simp [Atom.isError, hOpNotError]) hScan hPlan]
  simp only [List.length_cons, List.length_nil]
  rw [evaluateExpectedApplicationFrom_unary_eq_of_argumentFold_and_notReducible
    env fuel st stArg stRoot bnd op arg' out partBnd rootBnd
      (untypedTupleSelectedTypeFrom bnd 1) false hArguments
      (by
        intro _
        have hUndefined := instantiate_of_closed bnd (.sym "%Undefined%")
          (by simp [Atom.vars])
        change (if instantiate bnd (.sym "%Undefined%") == .sym "Expression"
          then .sym "%Undefined%" else instantiate bnd (.sym "%Undefined%")) =
            .sym "%Undefined%"
        rw [hUndefined]
        rfl)
      (by
        have hUndefined := instantiate_of_closed bnd (.sym "%Undefined%")
          (by simp [Atom.vars])
        change (instantiate bnd (.sym "%Undefined%") == .sym "Atom") = false
        rw [hUndefined]
        rfl)
      hNoChanged hRoot]
  simp

/-- Exact two-argument constructor congruence for the live expected-application
worker once its ordered argument fold has been computed.

The theorem is policy-data agnostic: callers supply the selected payload's
neutral result facts, the completed live row, and the root `NotReducible`
readout.  In particular, the row's bindings are preserved literally rather
than replaced by an empty-binding approximation. -/
theorem evaluateExpectedApplicationFrom_binary_eq_of_argumentFold_and_notReducible
    (env : MinEnv) (fuel : Nat) (st stArgs stRoot : St)
    (bnd : Bindings) (op : String)
    (first' second' firstOut secondOut : Atom)
    (partBnd rootBnd : Bindings) (selected : SelectedFunctionType)
    (returnAtom : Bool)
    (hArguments :
      expectedApplicationArgumentFold
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          bnd st [first', second'] selected =
        ([([firstOut, secondOut], partBnd)], stArgs))
    (hResultExpected :
      returnsAtom selected = false →
        selectedResultExpected selected = Atom.sym "%Undefined%")
    (hReturn : returnsAtom selected = returnAtom)
    (hNoChanged :
      (([firstOut, secondOut].zip [first', second']).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot :
      interpretFuel env (fuel + 1) stArgs
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval",
                Atom.expr [Atom.sym op, firstOut, secondOut]]) [],
             bnd := bnd }] [] =
        ([(notReducibleA, rootBnd)], stRoot)) :
    evaluateExpectedApplicationFrom
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack
                (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
        bnd st op [first', second'] selected =
      ([(Atom.expr [Atom.sym op, firstOut, secondOut], partBnd)], stRoot) := by
  rw [evaluateExpectedApplicationFrom_eq_factored]
  rw [evaluateExpectedApplicationFromFactored_eq_selectedResultFold_of_argumentFold
    (fun nextSt nextBindings nextAtom nextExpected =>
      mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
    (fun nextSt nextBindings nextAtom =>
      mettaEval env fuel nextSt nextBindings nextAtom)
    (fun nextSt application =>
      interpretFuel env (fuel + 1) nextSt
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", application]) [], bnd := bnd }] [])
    bnd st stArgs op [first', second'] selected
    [([firstOut, secondOut], partBnd)] hArguments hResultExpected
    (mettaEvalExpected_undefined env fuel)]
  rw [hReturn]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [selectedResultFoldStep_eq_mettaEvalExprPartFoldStep]
  unfold mettaEvalExprPartFoldStep
  rw [hNoChanged]
  simp only [List.nil_append]
  rw [hRoot]
  rw [mettaEvalExprRootFold_eq_of_notReducible_singleton]

/-- Live untyped-tuple specialization of the binary constructor theorem.

This is the two-argument sibling of
`mettaEval_unary_expr_eq_of_untypedTuple_argumentFold_and_notReducible_from`.
It consumes the exact live scan and argument fold and therefore remains valid
for nonempty incoming theories. -/
theorem mettaEval_binary_expr_eq_of_untypedTuple_argumentFold_and_notReducible_from
    (env : MinEnv) (fuel : Nat) (st stArgs stRoot : St)
    (bnd : Bindings) (op : String) (hOpNotError : op ≠ "Error")
    (first second first' second' firstOut secondOut : Atom)
    (partBnd rootBnd : Bindings)
    (hInst :
      instantiate bnd (Atom.expr [Atom.sym op, first, second]) =
        Atom.expr [Atom.sym op, first', second'])
    (hScan :
      selectFunctionType env st.world (.sym op) [first', second'] =
        .exhausted [] true)
    (hPlan : ApplicationPlanCorresponds bnd (.untypedTuple hScan))
    (hArguments :
      expectedApplicationArgumentFold
          (fun nextSt nextBindings nextAtom nextExpected =>
            mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
          bnd st [first', second'] (untypedTupleSelectedTypeFrom bnd 2) =
        ([([firstOut, secondOut], partBnd)], stArgs))
    (hNoChanged :
      (([firstOut, secondOut].zip [first', second']).find?
        (fun pair =>
          (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none)
    (hRoot :
      interpretFuel env (fuel + 1) stArgs
          [{ stack := atomToStack
              (Atom.expr [Atom.sym "eval",
                Atom.expr [Atom.sym op, firstOut, secondOut]]) [],
             bnd := bnd }] [] =
        ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st bnd
        (Atom.expr [Atom.sym op, first, second]) =
      ([(Atom.expr [Atom.sym op, firstOut, secondOut], partBnd)], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_untypedTuple_after_instantiate
    env fuel st bnd (Atom.expr [Atom.sym op, first, second]) op
      [first', second'] hInst
      (by simp [Atom.isError, hOpNotError]) hScan hPlan]
  simp only [List.length_cons, List.length_nil]
  rw [evaluateExpectedApplicationFrom_binary_eq_of_argumentFold_and_notReducible
    env fuel st stArgs stRoot bnd op first' second' firstOut secondOut
      partBnd rootBnd (untypedTupleSelectedTypeFrom bnd 2) false hArguments
      (by
        intro _
        have hUndefined := instantiate_of_closed bnd (.sym "%Undefined%")
          (by simp [Atom.vars])
        change (if instantiate bnd (.sym "%Undefined%") == .sym "Expression"
          then .sym "%Undefined%" else instantiate bnd (.sym "%Undefined%")) =
            .sym "%Undefined%"
        rw [hUndefined]
        rfl)
      (by
        have hUndefined := instantiate_of_closed bnd (.sym "%Undefined%")
          (by simp [Atom.vars])
        change (instantiate bnd (.sym "%Undefined%") == .sym "Atom") = false
        rw [hUndefined]
        rfl)
      hNoChanged hRoot]
  simp

theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy_of_no_changed_terminal
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNoChangedTerminal :
      ((out == emptyA || out.isError) && out != arg) = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
  simp [evaluateSelectedApplication, hMask, hArg, hNoChangedTerminal]
  have hrootDirect :
      interpretFuel env (fuel + 1) stArg
        [({ stack := atomToStack (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, out]]) [] } :
          Item)] [] = ([(notReducibleA, [])], stRoot) := by
    simpa [evalItemNil] using hroot
  rw [hrootDirect]
  change prioritizeSemanticResults
      (List.foldl
        (mettaEvalExprRootFoldStep env fuel arg.vars (Atom.expr [Atom.sym op, out])
          (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
          returnAtom)
        ([], stRoot) [(notReducibleA, [])]) =
    ([(Atom.expr [Atom.sym op, out],
        restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot)
  rw [mettaEvalExprRootFold_eq_of_notReducible_singleton
    env fuel arg.vars (Atom.expr [Atom.sym op, out])
    (restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))
    returnAtom [] stRoot]
  simp

/-- Nonterminal-output specialization of
`mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy_of_no_changed_terminal`.
This convenient form covers the common case while the general boundary also
admits an unchanged `Empty` result. -/
theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (mask : List Bool) (returnAtom : Bool)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [arg] mask returnAtom)
    (hMask : mask = [true])
    (hNotError : (out == emptyA || out.isError) = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  exact
    mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy_of_no_changed_terminal
      env fuel st stArg stRoot op hOpNotError arg out mask returnAtom hArg hPolicy hMask
      (by simp [hNotError]) hroot

/-- Selected-signature specialization of the exact unary policy theorem. -/
theorem mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq
    (env : MinEnv) (fuel : Nat) (st stArg stRoot : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
    (hroot : interpretFuel env (fuel + 1) stArg
      [evalItemNil (Atom.expr [Atom.sym op, out])] [] =
        ([(notReducibleA, [])], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg]) =
      ([(Atom.expr [Atom.sym op, out],
          restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))], stRoot) := by
  exact mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq_of_exactPolicy
    env fuel st stArg stRoot op hOpNotError arg out (argMask selected 1) (returnsAtom selected)
    hArg (.selected selected hSelected hPlan hNeutral) hMask hNotError hroot

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
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
    env fuel st op [x, y] mask returnAtom hPolicy hApplicationNotError]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hx]
  have hNoErrX :=
    changedArgumentStop_prefix_none [x'] [y'] [x, y] (by simpa using hNoErr)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErrX (by simp)
  simp [hxClosed, hyClosed, restrictBnd_nil_vars, hXNotChanged]
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
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
    (.selected selected hSelected hPlan hNeutral) hApplicationNotError hMask hNoErr hRoot hRootNotNotReducible
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
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnAtom = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x, y] mask returnAtom hPolicy hApplicationNotError]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [hx]
  have hNoErrX :=
    changedArgumentStop_prefix_none [x'] [y'] [x, y] (by simpa using hNoErr)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErrX (by simp)
  simp [hxClosed, hyClosed, restrictBnd_nil_vars, hXNotChanged]
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
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := hFinalNotError)
  exact List.mem_map.mpr ⟨(final, []), hFinal, rfl⟩

/-- Selected-signature specialization of the membership-shaped binary policy theorem. -/
theorem mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ stRoot : St)
    (op : String) (x y x' y' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval env fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval env fuel st₁ [] y = ([(y', [])], st₂))
    (hSelected : selectFunctionType env st.world (.sym op) [x, y] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 := by
  exact mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem_of_exactPolicy
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
    (argMask selected 2) (returnsAtom selected) hxClosed hyClosed hx hy
    (.selected selected hSelected hPlan hNeutral) hApplicationNotError hMask hNoErr hRoot
    hRootNotNotReducible hRootNotSelf hReturns hFinal hFinalNotError

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
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find?
      (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(Atom.expr [Atom.sym op, x', y'], [])], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x, y] (argMask selected 2) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) hApplicationNotError]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  rw [hx]
  have hNoErrX :=
    changedArgumentStop_prefix_none [x'] [y'] [x, y] (by simpa using hNoErr)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErrX (by simp)
  simp [hxClosed, hyClosed, restrictBnd_nil_vars, hXNotChanged]
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
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hScan : selectFunctionType env st.world (.sym op) [x, y] = .exhausted [] true)
    (hPlan : ApplicationPlanCorresponds [] (.untypedTuple hScan))
    (hNoErr : (([x', y'].zip [x, y]).find?
      (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(notReducibleA, rootBnd)], stRoot)) :
    mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y]) =
      ([(Atom.expr [Atom.sym op, x', y'], [])], stRoot) := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_untypedTuple
    env fuel st op [x, y] hApplicationNotError hScan hPlan]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop,
    List.replicate_succ, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.zip_cons_cons,
    List.foldl_cons, List.foldl_nil, List.nil_append]
  rw [hx]
  have hNoErrX :=
    changedArgumentStop_prefix_none [x'] [y'] [x, y] (by simpa using hNoErr)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErrX (by simp)
  simp [hxClosed, hyClosed, restrictBnd_nil_vars, hXNotChanged]
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
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom)
    (mask : List Bool) (returnAtom : Bool)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hPolicy : RecursionNeutralApplicationPolicy
      env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : (root, []) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnAtom = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  have hWNotChanged : ¬ (((w' == emptyA) = true ∨ w'.isError = true) ∧ (w' != w) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := w') (original := w) hNoErr (by simp)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y' == emptyA) = true ∨ y'.isError = true) ∧ (y' != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y') (original := y) hNoErr (by simp)
  rw [hw]
  simp [restrictBnd_empty_merge_empty, hWNotChanged]
  rw [hx]
  simp [restrictBnd_empty_merge_empty, hWNotChanged, hXNotChanged]
  rw [hy]
  simp [restrictBnd_empty_merge_empty, hWNotChanged, hXNotChanged, hYNotChanged]
  rw [hz]
  simp [restrictBnd_empty_merge_empty]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
      simpa [restrictBnd_empty_merge_empty, qvars] using hfold

/-- Selected-signature specialization of the quaternary empty-root policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom)
    (selected : SelectedFunctionType)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 4)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : (root, []) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact mettaEval_quaternary_expr_mem_of_arg_singletons_and_empty_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ st₃ st₄ op hOpNotError w x y z w' x' y' z' root final
    (argMask selected 4) (returnsAtom selected) hw hx hy hz
    (.selected selected hSelected hPlan hNeutral) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal hFinalNotError

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
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hPolicy : RecursionNeutralApplicationPolicy
      env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  have hWNotChanged : ¬ (((w' == emptyA) = true ∨ w'.isError = true) ∧ (w' != w) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := w') (original := w) hNoErr (by simp)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y' == emptyA) = true ∨ y'.isError = true) ∧ (y' != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y') (original := y) hNoErr (by simp)
  rw [hw]
  simp [restrictBnd_empty_merge_empty, hWNotChanged]
  rw [hx]
  simp [restrictBnd_empty_merge_empty, hWNotChanged, hXNotChanged]
  rw [hy]
  simp [restrictBnd_empty_merge_empty, hWNotChanged, hXNotChanged, hYNotChanged]
  rw [hz]
  simp [restrictBnd_empty_merge_empty]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
      simpa [qvars] using hfold

/-- Selected-signature specialization of the quaternary open-root policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 4)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact mettaEval_quaternary_expr_mem_of_arg_singletons_and_open_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ st₃ st₄ op hOpNotError w x y z w' x' y' z' root final rootBnd
    (argMask selected 4) (returnsAtom selected) hw hx hy hz
    (.selected selected hSelected hPlan hNeutral) hMask hNoErr hRoot hRootNotNotReducible
    hRootNotSelf hReturns hFinal hFinalNotError

/-- Membership-shaped four-argument expression fold for quoted arguments.

This is the executable scheduler shape for prelude operators whose signatures
mark all four arguments as `Atom`-like data, such as stdlib `unify`: the outer
`mettaEval` loop quotes all arguments, reduces the rebuilt root expression, and
then recursively evaluates the selected root readout.  Callers still supply the
operator's exact selected-signature witness, mask, and return policy rather
than forcing this generic theorem to unfold a large environment. -/
theorem mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member_of_exactPolicy
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z root final : Atom) (rootBnd : Bindings)
    (mask : List Bool) (returnAtom : Bool)
    (hPolicy : RecursionNeutralApplicationPolicy
      env st.world op [w, x, y, z] mask returnAtom)
    (hMask : mask = [false, false, false, false])
    (hNoErr :
      (([w, x, y, z].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  let qvars := ([w, x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] mask returnAtom hPolicy (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hWNotChanged : ¬ (((w == emptyA) = true ∨ w.isError = true) ∧ (w != w) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := w) (original := w) hNoErr (by simp)
  have hXNotChanged : ¬ (((x == emptyA) = true ∨ x.isError = true) ∧ (x != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x) (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y == emptyA) = true ∨ y.isError = true) ∧ (y != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y) (original := y) hNoErr (by simp)
  have hZNotChanged : ¬ (((z == emptyA) = true ∨ z.isError = true) ∧ (z != z) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := z) (original := z) hNoErr (by simp)
  simp [Metta.instantiate_nil, hWNotChanged, hXNotChanged, hYNotChanged,
    hZNotChanged]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
      simpa [qvars] using hfold

/-- Selected-signature specialization of the quoted quaternary policy theorem. -/
theorem mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 4)
    (hMask : argMask selected 4 = [false, false, false, false])
    (hNoErr :
      (([w, x, y, z].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([w, x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([w, x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  exact
    mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member_of_exactPolicy
      env fuel st op hOpNotError w x y z root final rootBnd
      (argMask selected 4) (returnsAtom selected)
      (.selected selected hSelected hPlan hNeutral) hMask hNoErr hRoot hRootNotNotReducible
      hRootNotSelf hReturns hFinal hFinalNotError

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
    (op : String) (hOpNotError : op ≠ "Error")
    (x y z root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 3)
    (hMask : argMask selected 3 = [false, false, false])
    (hNoErr :
      (([x, y, z].zip [x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([x, y, z]).flatMap Atom.vars)
          (((restrictBnd (([x, y, z]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y, z])).1 := by
  let qvars := ([x, y, z]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x, y, z] (argMask selected 3) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hXNotChanged : ¬ (((x == emptyA) = true ∨ x.isError = true) ∧ (x != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x) (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y == emptyA) = true ∨ y.isError = true) ∧ (y != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y) (original := y) hNoErr (by simp)
  have hZNotChanged : ¬ (((z == emptyA) = true ∨ z.isError = true) ∧ (z != z) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := z) (original := z) hNoErr (by simp)
  simp [Metta.instantiate_nil, hXNotChanged, hYNotChanged, hZNotChanged]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
      simpa [qvars] using hfold

/-- Membership-shaped one-argument expression fold for quoted arguments.

This is the executable scheduler shape for unary prelude operators whose signatures quote their
sole argument as data, reduce the rebuilt root expression, and then recursively evaluate the
selected root readout.  It is the unary companion to
`mettaEval_quaternary_expr_mem_of_quoted_args_and_open_root_eval_member`; callers provide the
operator's concrete signature and root-step facts. -/
theorem mettaEval_unary_expr_mem_of_quoted_arg_and_open_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (x root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hSelected : selectFunctionType env st.world (.sym op) [x] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [false])
    (hNoErr :
      (([x].zip [x]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
          root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd x.vars
          (((restrictBnd x.vars ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x])).1 := by
  let qvars := x.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [x] (argMask selected 1) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  simp [Metta.instantiate_nil]
  have hNoErr' :
      List.find? (fun ho : Atom × Atom => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)
        [(x, x)] = none := by
    simpa using hNoErr
  have hNoErrIf :
      (if (((x == emptyA) = true ∨ x.isError = true) ∧ (x != x) = true)
        then some (x, x) else none) = none := by
    simpa [Bool.or_eq_true] using hNoErr'
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
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
    (op : String) (hOpNotError : op ≠ "Error")
    (p atom templ atom' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArg : mettaEval env fuel st [] atom = ([(atom', [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [p, atom, templ] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 3)
    (hMask : argMask selected 3 = [false, true, false])
    (hNoErr :
      (([p, atom', templ].zip [p, atom, templ]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([p, atom, templ]).flatMap Atom.vars)
          (((restrictBnd (([p, atom, templ]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, p, atom, templ])).1 := by
  let qvars := p.vars ++ (atom.vars ++ templ.vars)
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [p, atom, templ] (argMask selected 3) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := p) (original := p) hNoErr (by simp)
  have hAtomNotChanged : ¬ (((atom' == emptyA) = true ∨ atom'.isError = true) ∧ (atom' != atom) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := atom') (original := atom) hNoErr (by simp)
  have hTemplNotChanged : ¬ (((templ == emptyA) = true ∨ templ.isError = true) ∧ (templ != templ) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := templ) (original := templ) hNoErr (by simp)
  simp [Metta.instantiate_nil, hPNotChanged]
  rw [hArg]
  simp [restrictBnd_empty_merge_empty, Metta.instantiate_nil,
    hPNotChanged, hAtomNotChanged, hTemplNotChanged]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
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
    (op : String) (hOpNotError : op ≠ "Error")
    (p atom templ atom' root final : Atom) (argPairs : List (Atom × Bindings))
    (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArg : mettaEval env fuel st [] atom = (argPairs, stArg))
    (hmemArg : (atom', []) ∈ argPairs)
    (hSelected : selectFunctionType env st.world (.sym op) [p, atom, templ] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 3)
    (hMask : argMask selected 3 = [false, true, false])
    (hNoErr :
      (([p, atom', templ].zip [p, atom, templ]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
                ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, p, atom, templ])).1 := by
  let qvars := p.vars ++ (atom.vars ++ templ.vars)
  let parts0 : List (List Atom × Bindings) :=
    argPairs.map (fun q : Atom × Bindings =>
      ([p, q.1], restrictBnd qvars ((Bindings.merge [] q.2).head?.getD q.2)))
  let completeTempl : (List Atom × Bindings) → (List Atom × Bindings) :=
    fun part0 =>
      match (part0.1.zip [p, atom, templ]).find?
          (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
      | some _ => part0
      | none => (part0.1 ++ [instantiate part0.2 templ], part0.2)
  let appendTempl :=
    fun acc2 : List (List Atom × Bindings) × St => fun part0 : List Atom × Bindings =>
      match (part0.1.zip [p, atom, templ]).find?
          (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
      | some _ => (acc2.1 ++ [part0], acc2.2)
      | none =>
          (acc2.1 ++ [(part0.1 ++ [instantiate part0.2 templ], part0.2)], acc2.2)
  let parts : List (List Atom × Bindings) :=
    parts0.map completeTempl
  let part : List Atom × Bindings := ([p, atom', templ], [])
  have hArg1 : (mettaEval env fuel st [] atom).1 = argPairs := by
    simp [hArg]
  have hArg2 : (mettaEval env fuel st [] atom).2 = stArg := by
    simp [hArg]
  have hNoErrSelectedPrefix :
      (([p, atom'].zip [p, atom, templ]).find?
        (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2)) = none :=
    changedArgumentStop_prefix_none [p, atom'] [templ] [p, atom, templ]
      (by simpa using hNoErr)
  have hpart : part ∈ parts := by
    refine List.mem_map.mpr ?_
    refine ⟨([p, atom'], []), ?_, ?_⟩
    refine List.mem_map.mpr ?_
    · exact ⟨(atom', []), hmemArg, by simp [qvars, restrictBnd_empty_merge_empty]⟩
    · simp only [completeTempl, part]
      rw [hNoErrSelectedPrefix]
      simp [Metta.instantiate_nil]
  have hNoErrPart :
      (part.1.zip [p, atom, templ]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) = none := by
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
            (pref ++ ps.map completeTempl, stArg) := by
      intro pref ps
      induction ps generalizing pref with
      | nil =>
          simp [appendTempl]
      | cons x xs ih =>
          have hstep :
              appendTempl (pref, stArg) x =
                (pref ++ [completeTempl x], stArg) := by
            unfold appendTempl completeTempl
            split <;> rfl
          rw [List.foldl_cons, hstep, ih]
          simp [List.append_assoc]
    simpa [parts] using hprepGen [] parts0
  have hprepRaw :
      List.foldl
          (fun acc2 part0 =>
            match (part0.1.zip [p, atom, templ]).find?
                (fun pair => (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2) with
            | some _ => (acc2.1 ++ [part0], acc2.2)
            | none =>
                (acc2.1 ++ [(part0.1 ++ [instantiate part0.2 templ], part0.2)], acc2.2))
          ([], stArg) parts0 =
        (parts, stArg) := by
    simpa only [appendTempl, completeTempl] using hprep
  have hPNotChanged : ¬ (((p == emptyA) = true ∨ p.isError = true) ∧ (p != p) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := p) (original := p) hNoErr (by simp)
  have hpartials :
      ([p, atom, templ].zip [false, true, false]).foldl
          (selectedArgumentFoldStep (mettaEval env fuel) qvars [p, atom, templ])
          ([([], [])], st) =
        (parts, stArg) := by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil]
    unfold selectedArgumentFoldStep
    simp only [List.foldl_cons, List.foldl_nil, List.zip_nil_left]
    simp [Metta.instantiate_nil, hPNotChanged]
    rw [hArg1, hArg2]
    simpa only [parts0, qvars] using hprepRaw
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [p, atom, templ] (argMask selected 3) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  rw [evaluateSelectedApplication_eq_factored]
  simp only [evaluateSelectedApplicationFactored, hMask]
  have hpartials' :
      ([p, atom, templ].zip [false, true, false]).foldl
          (selectedArgumentFoldStep
            (fun nextSt nextBindings nextAtom =>
              mettaEval env fuel nextSt nextBindings nextAtom)
            ([p, atom, templ].flatMap Atom.vars) [p, atom, templ])
          ([([], [])], st) =
        (parts, stArg) := by
    simpa [qvars] using hpartials
  rw [hpartials']
  have hstepEq :
      mettaEvalExprPartFoldStep env fuel qvars op [p, atom, templ] [] (returnsAtom selected) =
        (fun acc part =>
          match List.find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2) (part.1.zip [p, atom, templ]) with
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
  have hselectedStep :
      selectedResultFoldStep
          (fun nextSt nextBindings nextAtom =>
            mettaEval env fuel nextSt nextBindings nextAtom)
          (fun nextSt application =>
            interpretFuel env (fuel + 1) nextSt
              [{ stack := atomToStack
                  (Atom.expr [Atom.sym "eval", application]) [] }] [])
          ([p, atom, templ].flatMap Atom.vars) op [p, atom, templ]
          (returnsAtom selected) =
        mettaEvalExprPartFoldStep env fuel qvars op [p, atom, templ] []
          (returnsAtom selected) := by
    funext acc part0
    simpa [selectedResultFoldStep, mettaEvalExprPartFoldStep,
      mettaEvalExprRootFoldStep, qvars, Bool.or_eq_true] using
      (congrFun (congrFun hstepEq acc) part0).symm
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
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := hFinalNotError)
  rw [hselectedStep]
  simpa using hfold'

/-- Membership-shaped ternary expression fold for an evaluated/quoted/quoted argument mask.

This is the executable scheduler shape of stdlib `if`: evaluate the Boolean
condition, quote both branches, reduce the rebuilt root expression, then
recursively evaluate the selected branch.  As with the other scheduler folds,
the theorem is generic in the operator and environment; callers provide the
operator's concrete signature facts. -/
theorem mettaEval_ternary_expr_mem_of_eval_quoted_quoted_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st stCond : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (cond thenA elseA cond' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hCond : mettaEval env fuel st [] cond = ([(cond', [])], stCond))
    (hSelected : selectFunctionType env st.world (.sym op) [cond, thenA, elseA] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 3)
    (hMask : argMask selected 3 = [true, false, false])
    (hNoErr :
      (([cond', thenA, elseA].zip [cond, thenA, elseA]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
            ((Bindings.merge [] rootBnd).head?.getD rootBnd)) root).1)
    (hFinalNotError : final.isError = false) :
    (final,
        restrictBnd (([cond, thenA, elseA]).flatMap Atom.vars)
          (((restrictBnd (([cond, thenA, elseA]).flatMap Atom.vars)
              ((Bindings.merge [] rootBnd).head?.getD rootBnd)).merge
              ([] : Bindings)).head?.getD [])) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, cond, thenA, elseA])).1 := by
  let qvars := ([cond, thenA, elseA]).flatMap Atom.vars
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [cond, thenA, elseA] (argMask selected 3) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hCondNotChanged : ¬ (((cond' == emptyA) = true ∨ cond'.isError = true) ∧ (cond' != cond) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := cond') (original := cond) hNoErr (by simp)
  have hThenNotChanged : ¬ (((thenA == emptyA) = true ∨ thenA.isError = true) ∧ (thenA != thenA) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := thenA) (original := thenA) hNoErr (by simp)
  have hElseNotChanged : ¬ (((elseA == emptyA) = true ∨ elseA.isError = true) ∧ (elseA != elseA) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := elseA) (original := elseA) hNoErr (by simp)
  rw [hCond]
  simp [restrictBnd_empty_merge_empty, hCondNotChanged]
  rw [Metta.instantiate_nil thenA]
  simp [Metta.instantiate_nil, hCondNotChanged, hThenNotChanged,
    hElseNotChanged]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
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
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hwClosed : w.vars = []) (hxClosed : x.vars = [])
    (hyClosed : y.vars = []) (hzClosed : z.vars = [])
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 4)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : (root, rootBnd) ∈
      (interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] (argMask selected 4) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hWNotChanged : ¬ (((w' == emptyA) = true ∨ w'.isError = true) ∧ (w' != w) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := w') (original := w) hNoErr (by simp)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y' == emptyA) = true ∨ y'.isError = true) ∧ (y' != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y') (original := y) hNoErr (by simp)
  rw [hw]
  simp [hwClosed, hxClosed, hyClosed, hzClosed, restrictBnd_nil_vars,
    hWNotChanged]
  rw [hx]
  simp [hWNotChanged, hXNotChanged]
  rw [hy]
  simp [hWNotChanged, hXNotChanged, hYNotChanged]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
      simpa [restrictBnd_nil_vars] using hfold

/-- Exact-state closed four-argument expression fold for executable `mettaEval`.

This is the state-specific sibling of
`mettaEval_quaternary_expr_mem_of_arg_singletons_and_root_eval_member`.  It is useful when the
selected root readout is known exactly, so the recursive evaluation premise only has to hold at the
actual threaded root state rather than for every possible `World`. -/
theorem mettaEval_quaternary_expr_mem_of_arg_singletons_and_root_eval_eq
    (env : MinEnv) (fuel : Nat) (st st₁ st₂ st₃ st₄ stRoot : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (w x y z w' x' y' z' root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hwClosed : w.vars = []) (hxClosed : x.vars = [])
    (hyClosed : y.vars = []) (hzClosed : z.vars = [])
    (hw : mettaEval env fuel st [] w = ([(w', [])], st₁))
    (hx : mettaEval env fuel st₁ [] x = ([(x', [])], st₂))
    (hy : mettaEval env fuel st₂ [] y = ([(y', [])], st₃))
    (hz : mettaEval env fuel st₃ [] z = ([(z', [])], st₄))
    (hSelected : selectFunctionType env st.world (.sym op) [w, x, y, z] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 4)
    (hMask : argMask selected 4 = [true, true, true, true])
    (hNoErr :
      (([w', x', y', z'].zip [w, x, y, z]).find?
        (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₄
        [evalItemNil (Atom.expr [Atom.sym op, w', x', y', z'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, w', x', y', z']) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈
      (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, w, x, y, z])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [w, x, y, z] (argMask selected 4) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp only [evaluateSelectedApplication, firstChangedArgumentStop, hMask,
    List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  have hWNotChanged : ¬ (((w' == emptyA) = true ∨ w'.isError = true) ∧ (w' != w) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := w') (original := w) hNoErr (by simp)
  have hXNotChanged : ¬ (((x' == emptyA) = true ∨ x'.isError = true) ∧ (x' != x) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := x') (original := x) hNoErr (by simp)
  have hYNotChanged : ¬ (((y' == emptyA) = true ∨ y'.isError = true) ∧ (y' != y) = true) :=
    argument_not_changed_terminal_of_mem_zip
      (result := y') (original := y) hNoErr (by simp)
  rw [hw]
  simp [hwClosed, hxClosed, hyClosed, hzClosed, restrictBnd_nil_vars,
    hWNotChanged]
  rw [hx]
  simp [hWNotChanged, hXNotChanged]
  rw [hy]
  simp [hWNotChanged, hXNotChanged, hYNotChanged]
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
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := hFinalNotError)
  exact List.mem_map.mpr ⟨(final, []), hFinal, rfl⟩

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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg out : Atom) (selected : SelectedFunctionType)
    (R : Atom → Atom → Prop)
    (hArg : mettaEval env fuel st [] arg = ([(out, [])], stArg))
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [true])
    (hNotError : (out == emptyA || out.isError) = false)
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
      env fuel st stArg stRoot op hOpNotError arg out selected hArg hSelected hPlan
        hNeutral hMask hNotError hroot
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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [false])
    (hRoot : interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, arg]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] (argMask selected 1) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
  simp [evaluateSelectedApplication, hMask, hArgClosed, hArgNoErr, hArgSelf, instantiate_nil]
  have hRoot' :
      interpretFuel env (fuel + 1) st
        [{ stack := atomToStack
            (Atom.expr [Atom.sym "eval", Atom.expr [Atom.sym op, arg]]) [], bnd := [] }] [] =
      ([(root, rootBnd)], stRoot) := by
    simpa [evalItemNil] using hRoot
  rw [hRoot']
  simp [hRootNotNotReducible, hRootNotSelf, hReturns, restrictBnd_nil_vars]
  apply mem_prioritizeSemanticResults_of_mem_of_not_error
    (hError := hFinalNotError)
  exact List.mem_map.mpr
    ⟨(final, []), by simpa [restrictBnd_nil_vars] using hFinal, rfl⟩

/-- Membership-shaped unary fold for Atom-typed arguments and selected root readouts.

This is the root-membership companion to
`mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_mem`: it is the right shape when the
root equality-rule bridge supplies the runtime-freshened readout as a member rather than proving
the whole root-readout list is a singleton. -/
theorem mettaEval_unary_expr_mem_of_closed_atom_arg_and_root_eval_member
    (env : MinEnv) (fuel : Nat) (st : St)
    (op : String) (hOpNotError : op ≠ "Error")
    (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
    (hMask : argMask selected 1 = [false])
    (hRoot : (root, rootBnd) ∈ (interpretFuel env (fuel + 1) st
        [evalItemNil (Atom.expr [Atom.sym op, arg])] []).1)
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, arg]) = false)
    (hReturns : returnsAtom selected = false)
    (hFinal : ∀ st0, (final, []) ∈ (mettaEval env fuel st0 [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] (argMask selected 1) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
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
    (op : String) (hOpNotError : op ≠ "Error")
    (arg root final : Atom) (rootBnd : Bindings)
    (selected : SelectedFunctionType)
    (P : St → Prop)
    (hArgClosed : arg.vars = [])
    (hArgNoErr : arg.isError = false)
    (hArgSelf : (arg != arg) = false)
    (hSelected : selectFunctionType env st.world (.sym op) [arg] = .selected selected)
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hNeutral : SelectedApplicationRecursionNeutral selected 1)
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
      P st0 → (final, []) ∈ (mettaEval env fuel st0 [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, arg])).1 := by
  rw [mettaEval_eq_evaluateSelectedApplication_of_exactPolicy
    env fuel st op [arg] (argMask selected 1) (returnsAtom selected)
    (.selected selected hSelected hPlan hNeutral) (by simp [Atom.isError, hOpNotError])]
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
      apply mem_prioritizeSemanticResults_of_mem_of_not_error
        (hError := hFinalNotError)
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
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
      selected hxClosed hyClosed hx hy hSelected hPlan hApplicationNotError hNeutral hMask hNoErr hRoot
      hRootNotNotReducible hRootNotSelf hReturns hFinal
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
    (hPolicy : RecursionNeutralApplicationPolicy env st.world op [x, y] mask returnAtom)
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hMask : mask = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnAtom = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false)
    (hFinalReach : Relation.ReflTransGen R root final) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final := by
  constructor
  · exact
      mettaEval_binary_expr_mem_of_arg_singletons_and_root_eval_mem_of_exactPolicy
        env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
        mask returnAtom hxClosed hyClosed hx hy hPolicy hApplicationNotError hMask hNoErr hRoot
        hRootNotNotReducible hRootNotSelf hReturns hFinal hFinalNotError
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
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel env (fuel + 1) st₂
        [evalItemNil (Atom.expr [Atom.sym op, x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == Atom.expr [Atom.sym op, x', y']) = false)
    (hReturns : returnsAtom selected = false)
    (hRootReach : Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) root)
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false)
    (hFinalReach : Relation.ReflTransGen R root final) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final := by
  exact mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member_of_exactPolicy
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd
    (argMask selected 2) (returnsAtom selected) R hxClosed hyClosed hx hy
    (.selected selected hSelected hPlan hNeutral) hApplicationNotError hMask hNoErr hRoot
    hRootNotNotReducible hRootNotSelf hReturns hRootReach hFinal hFinalNotError hFinalReach

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
    (hPlan : ApplicationPlanCorresponds [] (.selected selected hSelected))
    (hApplicationNotError : (Atom.expr [Atom.sym op, x, y]).isError = false)
    (hNeutral : SelectedApplicationRecursionNeutral selected 2)
    (hMask : argMask selected 2 = [true, true])
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => (ho.1 == emptyA || ho.1.isError) && ho.1 != ho.2)) = none)
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
    (hFinal : (final, []) ∈ (mettaEval env fuel stRoot [] root).1)
    (hFinalNotError : final.isError = false) :
    (final, []) ∈ (mettaEval env (fuel + 1) st [] (Atom.expr [Atom.sym op, x, y])).1 ∧
      Relation.ReflTransGen R (Atom.expr [Atom.sym op, x, y]) final :=
  mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
    env fuel st st₁ st₂ stRoot op x y x' y' root final rootBnd selected R
    hxClosed hyClosed hx hy hSelected hPlan hApplicationNotError hNeutral hMask hNoErr hRoot
    hRootNotNotReducible hRootNotSelf hReturns hRootReach hFinal hFinalNotError
    (hFinalSound final hFinal)

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
