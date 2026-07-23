/-
# World preservation for the interpreter's non-recursive workers

The state-free capstone splits along a line the source draws for us, and this
module establishes the easy side of it in full.

Reading the runtime, the workers that `interpretStack1` delegates to —
`queryOp`, `evalOp`, and the space-atom freshener — never write the world.  They
thread `St` only to advance the **gensym counter**:

* `queryOpFoldStep` returns `(acc.1 ++ items, { acc.2 with counter := nextCounter })`
* `freshenSpaceAtoms`' fold returns `(renamed.1 :: acc.1, { acc.2 with counter := nextCounter })`

Both are counter-only record updates; neither mentions `world`.  Consequently
their world preservation is UNCONDITIONAL: it needs no environment closure, no
safety hypothesis on the atom, and no fuel.

That is the structurally important fact for the capstone.  World preservation
for a whole step does NOT require the producer closures at all — it requires
only that the step never reaches a world-mutating arm (nine head symbols,
spanning eight top-level arms and eleven `St.mapWorld` sites), plus
preservation of the genuinely recursive calls.  The producer closures
(`StrictGlobalProfile`, and the matcher/merge provenance API) are what the
OTHER certificate obligation needs: that successors of a reached configuration
are themselves reached.  Keeping the two apart is what stops the invariant from
being over-strengthened.
-/
import Mettapedia.Languages.MeTTa.HE.StateFreeExecution
import Mettapedia.Languages.MeTTa.HE.MatcherProvenance
import MettaHyperonFull.Proofs.WorldLaws
import MettaHyperonFull.Proofs.IndexingComplete

namespace Mettapedia.Languages.MeTTa.HE.StateFreeInterpreterSteps

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE.StateFreeFragment
open Mettapedia.Languages.MeTTa.HE.StateFreePreservation
open Mettapedia.Languages.MeTTa.HE.MatcherProvenance

/-! ## The query fold

`queryOp` folds `queryOpFoldStep` over the candidate rules.  Each step appends
work items and advances the counter; the world is carried through untouched. -/

/-- One query fold step leaves the world alone. -/
@[simp] theorem queryOpFoldStep_world (prev : Stack) (toEval : Atom)
    (b : Bindings) (acc : List Item × St) (rule : Atom × Atom) :
    (queryOpFoldStep prev toEval b acc rule).2.world = acc.2.world := rfl

/-- Folding the query step over any candidate list leaves the world alone. -/
theorem queryOpFold_world (prev : Stack) (toEval : Atom) (b : Bindings) :
    ∀ (rules : List (Atom × Atom)) (acc : List Item × St),
      (rules.foldl (queryOpFoldStep prev toEval b) acc).2.world = acc.2.world := by
  intro rules
  induction rules with
  | nil => intro acc; rfl
  | cons rule rest ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (queryOpFoldStep prev toEval b acc rule), queryOpFoldStep_world]

/-- **`queryOp` never writes the world.**  Unconditional: no environment
closure, no safety hypothesis, no fuel. -/
theorem queryOp_preservesWorld (env : MinEnv) (st : St) (prev : Stack)
    (toEval : Atom) (b : Bindings) :
    (queryOp env st prev toEval b).2.world = st.world := by
  rw [queryOp]
  by_cases hvar : isVariableHeaded toEval = true
  · simp [hvar]
  · have hfold : ((candidatesW env st.world toEval).foldl
        (queryOpFoldStep prev toEval b) ([], st)).2.world = st.world :=
      queryOpFold_world prev toEval b _ ([], st)
    simp only [hvar, Bool.false_eq_true, if_false]
    split
    · exact hfold
    · exact hfold

/-- **`evalOp` never writes the world.**  Every arm either returns the incoming
state or delegates to `queryOp`. -/
theorem evalOp_preservesWorld (env : MinEnv) (st : St) (prev : Stack)
    (x : Atom) (b : Bindings) :
    (evalOp env st prev x b).2.world = st.world := by
  simp only [evalOp]
  repeat' split
  all_goals first
    | rfl
    | exact queryOp_preservesWorld env st prev _ b

/-! ## Consequences for the certificate

With the workers settled, the `preserves` obligation for any branch that
delegates to them is discharged without reference to the environment.  These
are the reusable boundary facts the capstone consumes. -/

/-- The world after a query is the world before it, as a state-level equation
usable by rewriting. -/
theorem queryOp_world_eq (env : MinEnv) (st : St) (prev : Stack)
    (toEval : Atom) (b : Bindings) {w : World} (hw : st.world = w) :
    (queryOp env st prev toEval b).2.world = w := by
  rw [queryOp_preservesWorld, hw]

/-- Likewise for evaluation. -/
theorem evalOp_world_eq (env : MinEnv) (st : St) (prev : Stack)
    (x : Atom) (b : Bindings) {w : World} (hw : st.world = w) :
    (evalOp env st prev x b).2.world = w := by
  rw [evalOp_preservesWorld, hw]

/-! ## A genuinely pending evaluation step

Not a finished frame: the item below is `fin := false`, so `interpretStack1`
takes the `eval` arm and performs a real evaluation step.  Its world
preservation follows from `evalOp_preservesWorld` and holds for EVERY
environment — including the full prelude, whose mutation-capable rules are
present but unreached. -/

/-- A pending evaluation item: `(eval a)`, not yet finished. -/
def pendingEvalItem : Item :=
  { stack := [{ atom := Atom.expr [Atom.sym "eval", Atom.sym "a"], fin := false }],
    bnd := [] }

/-- It really is pending — outside the finished-frame class entirely. -/
theorem pendingEvalItem_not_isFinal : isFinal pendingEvalItem = false := rfl

/-- **A real evaluation step preserves the world**, for any environment and any
fuel.  This is the pending positive canary: the step goes through `evalOp`, not
through a return arm. -/
theorem pendingEvalItem_step_preservesWorld (env : MinEnv) (fuel : Nat) (st : St) :
    (interpretStack1 env fuel st pendingEvalItem).2.world = st.world := by
  simp only [interpretStack1, pendingEvalItem]
  exact evalOp_preservesWorld env st [] (Atom.sym "a") []

/-- The same step in the genuine prelude environment. -/
theorem fullPrelude_pendingEval_preservesWorld (fuel : Nat) (st : St) :
    (interpretStack1 StateFreeExecution.fullPreludeEnv fuel st pendingEvalItem).2.world
      = st.world :=
  pendingEvalItem_step_preservesWorld _ fuel st

/-! ## The freshening worker

`get-atoms` alpha-renames the atoms it returns, threading `St` through
`freshenSpaceAtoms` (`Interpreter.lean:373`).  That fold is counter-only too
(`{ acc.2 with counter := nextCounter }` at `:376`), so the branch is pure. -/

theorem freshenFold_world (avoid : List VarName) :
    ∀ (atoms : List Atom) (acc : List Atom × St),
      (atoms.foldl (fun (acc : List Atom × St) a =>
        let (renamed, nextCounter) := freshenRuleAvoiding acc.2.counter avoid a a
        (renamed.1 :: acc.1, { acc.2 with counter := nextCounter })) acc).2.world
        = acc.2.world := by
  intro atoms
  induction atoms with
  | nil => intro acc; rfl
  | cons a rest ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]

/-- **`freshenSpaceAtoms` never writes the world.** -/
theorem freshenSpaceAtoms_preservesWorld (st : St) (avoid : List VarName)
    (atoms : List Atom) :
    (freshenSpaceAtoms st avoid atoms).2.world = st.world := by
  rw [freshenSpaceAtoms]
  exact freshenFold_world avoid atoms ([], st)

/-! ## The conjunctive matcher

`matchConj`'s recursion lives in a helper, so its world preservation belongs on
the runtime's own proof boundary rather than here: it is proved once in
`MettaHyperonFull.Proofs.WorldLaws` as `matchConj_preservesWorld` and consumed
below.  This module names only the public wrapper, so an upstream change to the
helper cannot break it silently. -/

/-- The `match` arm: solutions are filtered, and the threaded state comes from
`matchConj`, which the runtime's world laws show is counter-only. -/
theorem interpretStack1_preservesWorld_match (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (space pattern template : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "match", space, pattern, template]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact Metta.matchConj_preservesWorld _ _ st _

/-! ## Per-arm preservation

The undirected sweep over `interpretStack1` is expensive for a mechanical
reason: Lean generates a SINGLE equation lemma for the whole definition
(`interpretStack1.eq_1` is the entire body; there is no `eq_2`), so unfolding
it once per branch re-elaborates the whole match each time.

Supplying the guard first makes each arm cheap, because the match reduces
immediately.  The arms below are representative of the bulk of the definition —
every non-mutating, non-recursive arm has this same shape, returning the
incoming state beside a freshly built item list. -/

/-- `unify` returns the incoming state: the operation is on items only. -/
theorem interpretStack1_preservesWorld_unify (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (a p t e : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "unify", a, p, t, e]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `cons-atom` on a well-formed argument pair. -/
theorem interpretStack1_preservesWorld_consAtom (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (h : Atom) (t : List Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "cons-atom", h, Atom.expr t]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `context-space` is a pure constant. -/
theorem interpretStack1_preservesWorld_contextSpace (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "context-space"]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `get-doc` reads the world without writing it. -/
theorem interpretStack1_preservesWorld_getDoc (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (x : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "get-doc", x]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `superpose-bind` only fans the item list out. -/
theorem interpretStack1_preservesWorld_superposeBind (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (pairs : List Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "superpose-bind", Atom.expr pairs]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-! ## Opaque binding payload safety

World preservation for `superpose-bind` is unconditional, but the reached
configuration invariant also needs a producer fact.  A well-formed collapsed
pair restores its stored bindings and merges them with the continuation
bindings; malformed pairs follow the runtime's non-reducing fallback.  Both
paths preserve the state-free invariant. -/

/-- Every item emitted by `superposeItems` is state-operation-free when the
input alternative, continuation, and current bindings are safe.  The opaque
payload case uses the exact store/restore boundary and matcher-provenance merge
closure; it is not treated as an inert grounded leaf. -/
theorem superposeItems_stateOpFree {prev : Stack} {current : Bindings}
    {encoded : Atom}
    (prevSafe : StackStateOpFree prev)
    (currentSafe : BindingsStateOpFree current)
    (encodedSafe : StateOpFree encoded) :
    ∀ item ∈ superposeItems prev current encoded, ItemStateOpFree item := by
  intro item member
  cases encoded with
  | sym name =>
      simp only [superposeItems, List.mem_singleton] at member
      subst item
      exact finItem_stateOpFree prevSafe encodedSafe currentSafe
  | var name =>
      simp only [superposeItems, List.mem_singleton] at member
      subst item
      exact finItem_stateOpFree prevSafe encodedSafe currentSafe
  | gnd ground =>
      simp only [superposeItems, List.mem_singleton] at member
      subst item
      exact finItem_stateOpFree prevSafe encodedSafe currentSafe
  | expr atoms =>
      cases atoms with
      | nil =>
          simp only [superposeItems, List.mem_singleton] at member
          subst item
          exact finItem_stateOpFree prevSafe encodedSafe currentSafe
      | cons atom tail =>
          have atomSafe : StateOpFree atom :=
            stateOpFree_of_mem encodedSafe.2 (by simp)
          cases tail with
          | nil =>
              simp only [superposeItems, List.mem_singleton] at member
              subst item
              exact finItem_stateOpFree prevSafe atomSafe currentSafe
          | cons payload rest =>
              cases rest with
              | cons third rest =>
                  simp only [superposeItems, List.mem_singleton] at member
                  subst item
                  exact finItem_stateOpFree prevSafe atomSafe currentSafe
              | nil =>
                  cases payload with
                  | sym name =>
                      simp only [superposeItems, List.mem_singleton] at member
                      subst item
                      exact finItem_stateOpFree prevSafe atomSafe currentSafe
                  | var name =>
                      simp only [superposeItems, List.mem_singleton] at member
                      subst item
                      exact finItem_stateOpFree prevSafe atomSafe currentSafe
                  | expr payloadAtoms =>
                      simp only [superposeItems, List.mem_singleton] at member
                      subst item
                      exact finItem_stateOpFree prevSafe atomSafe currentSafe
                  | gnd ground =>
                      cases ground with
                      | bindings stored =>
                          simp only [superposeItems] at member
                          obtain ⟨merged, mergedMember, emitted⟩ :=
                            List.mem_filterMap.mp member
                          split at emitted
                          · contradiction
                          · cases emitted
                            apply finItem_stateOpFree prevSafe atomSafe
                            exact merge_bindingsStateOpFree
                              (StateFreePreservation.storedBindings_restore_stateOpFree
                                stored encodedSafe.2.2.1)
                              currentSafe merged mergedMember
                      | int value =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | float value =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | str value =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | bool value =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | unit =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | error message =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe
                      | external typeName payload =>
                          simp only [superposeItems, List.mem_singleton] at member
                          subst item
                          exact finItem_stateOpFree prevSafe atomSafe currentSafe

/-- `eval` delegates to the worker, which is already known pure. -/
theorem interpretStack1_preservesWorld_eval (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (x : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "eval", x]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  exact evalOp_preservesWorld env st prev x it.bnd

/-- `chain` rewrites the stack only. -/
theorem interpretStack1_preservesWorld_chain (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (nested : Atom) (v : VarName) (templ : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "chain", nested, Atom.var v, templ]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `decons-atom` on a non-empty expression. -/
theorem interpretStack1_preservesWorld_deconsAtom (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (h : Atom) (t : List Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "decons-atom", Atom.expr (h :: t)]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack, hfin, hatom]

/-- `get-state` READS the world; both its arms return the incoming state. -/
theorem interpretStack1_preservesWorld_getState (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (s : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "get-state", s]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals rfl

/-- `get-atoms` freshens what it returns; the freshener is counter-only. -/
theorem interpretStack1_preservesWorld_getAtoms (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (s : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "get-atoms", s]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact freshenSpaceAtoms_preservesWorld st _ _

/-- `evalc` delegates to `evalOp` in a space-selected environment. -/
theorem interpretStack1_preservesWorld_evalc (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (x space : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "evalc", x, space]) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact evalOp_preservesWorld _ st prev x it.bnd

/-- The catch-all arm: an unsupported embedded op, or marking the frame
finished.  Both return the incoming state. -/
theorem interpretStack1_preservesWorld_fallback (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hother : ∀ (head : String) (rest : List Atom),
      top.atom ≠ Atom.expr (Atom.sym head :: rest)) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact absurd ‹_› (hother _ _)

/-! ## The type-service emit fold

`get-type` and `get-type-space` share one closure: they fold `mettaEval` over
the candidate types, threading the state.  The fold itself contributes no world
change, so its preservation reduces entirely to the evaluator's.

The `mettaEval` fact is taken as a parameter rather than proved here, because
`mettaEval` is a member of the interpreter's mutual recursion group: at the use
site inside the four-way functional induction it is discharged by the case's
own induction hypothesis.  This lemma is the reusable shape that lets the IH be
applied under a fold. -/

theorem emitFold_world (typeEnv : MinEnv) (fuel : Nat) (bnd : Bindings)
    (prev : Stack) (hbnd : BindingsStateOpFree bnd)
    (hstep : ∀ (acc : List Item × St) (t : Atom), StateOpFree t →
      BindingsStateOpFree bnd →
      (mettaEval typeEnv fuel acc.2 bnd t).2.world = acc.2.world) :
    ∀ (types : List Atom), (∀ t ∈ types, StateOpFree t) →
      ∀ (acc : List Item × St),
      (types.foldl (fun (acc : List Item × St) t =>
        match mettaEval typeEnv fuel acc.2 bnd t with
        | (rs, st2) => (acc.1 ++ rs.map (fun p => finItem prev p.1 bnd), st2))
        acc).2.world = acc.2.world := by
  intro types
  induction types with
  | nil => intro _ acc; rfl
  | cons t rest ih =>
      intro htypes acc
      simp only [List.foldl_cons]
      rw [ih (fun s hs => htypes s (by simp [hs]))]
      exact hstep acc t (htypes t (by simp)) hbnd

/-! ## The type-service arms

`get-type` and `get-type-space` share a body: parse the arguments, then emit
either nothing or the `emit` fold.  Every leaf is therefore the incoming state
or a fold of `mettaEval`, so the whole arm reduces to the evaluator fact.

That fact is a PARAMETER, not an assumption about the arm's own conclusion: at
the use site inside the four-way functional induction it is discharged by the
case's induction hypothesis for `mettaEval`. -/

/-- The `get-type` arm preserves the world whenever the evaluator does. -/
theorem interpretStack1_preservesWorld_getType (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (args : List Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr (Atom.sym "get-type" :: args))
    (hbnd : BindingsStateOpFree it.bnd)
    (htypes : ∀ (typeEnv : MinEnv) (x : Atom) (t : Atom),
      t ∈ getTypes typeEnv (typePrep st.world x) → StateOpFree t)
    (hEval : ∀ (typeEnv : MinEnv) (acc : List Item × St) (t : Atom), StateOpFree t →
      BindingsStateOpFree it.bnd →
      (mettaEval typeEnv fuel acc.2 it.bnd t).2.world = acc.2.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact emitFold_world _ fuel it.bnd prev hbnd (fun acc t ht hb => hEval _ acc t ht hb)
        _ (fun t ht => htypes _ _ t ht) ([], st)

/-- The `get-type-space` arm, same body, same reduction. -/
theorem interpretStack1_preservesWorld_getTypeSpace (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (args : List Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr (Atom.sym "get-type-space" :: args))
    (hbnd : BindingsStateOpFree it.bnd)
    (htypes : ∀ (typeEnv : MinEnv) (x : Atom) (t : Atom),
      t ∈ getTypes typeEnv (typePrep st.world x) → StateOpFree t)
    (hEval : ∀ (typeEnv : MinEnv) (acc : List Item × St) (t : Atom), StateOpFree t →
      BindingsStateOpFree it.bnd →
      (mettaEval typeEnv fuel acc.2 it.bnd t).2.world = acc.2.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact emitFold_world _ fuel it.bnd prev hbnd (fun acc t ht hb => hEval _ acc t ht hb)
        _ (fun t ht => htypes _ _ t ht) ([], st)

/-! ## The recursive arms

Four arms call a sibling of the interpreter's mutual recursion group.  Each is
stated with that sibling's world-preservation as a PARAMETER, so the arm can be
proved once, cheaply, and then APPLIED inside the four-way functional induction
with the case's own induction hypothesis supplying the parameter.  No
recursive-call hypothesis survives into any public statement below. -/

/-- `capture` evaluates its argument and relabels the results. -/
theorem interpretStack1_preservesWorld_capture (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (atom : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "capture", atom])
    (hEval : ∀ (st' : St), (mettaEval env fuel st' it.bnd atom).2.world = st'.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  exact hEval st

/-- `metta-thread` evaluates and then re-merges bindings; same state source. -/
theorem interpretStack1_preservesWorld_mettaThread (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (atom typ space : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "metta-thread", atom, typ, space])
    (hEval : ∀ (st' : St), (mettaEval env fuel st' it.bnd atom).2.world = st'.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  exact hEval st

/-- `collapse-bind` runs a nested interpreter loop and collapses its results. -/
theorem interpretStack1_preservesWorld_collapseBind (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (nested : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "collapse-bind", nested])
    (hLoop : ∀ (st' : St),
      (interpretFuel env fuel st'
        [{ stack := atomToStack nested [], bnd := it.bnd }] []).2.world = st'.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  exact hLoop st

/-- `metta` type-checks its argument; all but one of its leaves return the
incoming state, and the remaining one delegates to `mettaEvalExpected`. -/
theorem interpretStack1_preservesWorld_metta (env : MinEnv) (fuel : Nat) (st : St)
    (it : Item) (top : Frame) (prev : Stack) (atom typ space : Atom)
    (hstack : it.stack = top :: prev) (hfin : top.fin = false)
    (hatom : top.atom = Atom.expr [Atom.sym "metta", atom, typ, space])
    (hExpected : ∀ (selectedEnv : MinEnv) (st' : St) (a e : Atom),
      (mettaEvalExpected selectedEnv fuel st' it.bnd a e).2.world = st'.world) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, hatom, Bool.false_eq_true, if_false]
  repeat' split
  all_goals first
    | rfl
    | exact hExpected _ st _ _

/-! ## Environment closure for a derived environment

`typeEnvForSpace` and `evalEnvForSpace` rebuild a `MinEnv` with
`MinEnv.ofAtomsGT`, whose rule index, type table and expression-type table are
all DERIVED from the atom list.  Establishing `MinEnvStateOpFree` for such an
environment therefore reduces to the atom list, one derived structure at a
time.  The rule side reduces cleanly because the runtime already proves
`candidates_sound`: every offered candidate came from `extractRules`. -/

/-- `extractRules` only ever hands back subterms of `(= lhs rhs)` atoms, so a
safe atom list yields safe rules. -/
theorem extractRules_safe {atoms : List Atom} (hatoms : StateOpFreeList atoms) :
    ∀ r ∈ extractRules atoms, StateOpFree r.1 ∧ StateOpFree r.2 := by
  intro r hr
  obtain ⟨a, hmem, hEq⟩ := List.mem_filterMap.mp hr
  have hsafe : StateOpFree a := stateOpFree_of_mem hatoms hmem
  split at hEq
  · simp only [Option.some.injEq] at hEq
    subst hEq
    exact ⟨hsafe.2.2.1, hsafe.2.2.2.1⟩
  · simp at hEq

/-- **The `candidates` field of `MinEnvStateOpFree`, for any derived
environment.**  Uses the runtime's own soundness of first-argument indexing, so
no `HashMap` reasoning is needed here. -/
theorem ofAtomsGT_candidates_safe {atoms : List Atom} {gt : GroundingTable}
    (hatoms : StateOpFreeList atoms) :
    ∀ (query lhs rhs : Atom), StateOpFree query →
      (lhs, rhs) ∈ (MinEnv.ofAtomsGT atoms gt).candidates query →
      StateOpFree lhs ∧ StateOpFree rhs := by
  intro query lhs rhs _ hmem
  exact extractRules_safe hatoms (lhs, rhs)
    (Metta.candidates_sound atoms gt query (lhs, rhs) hmem)

/-! ### The symbol-type table

Unlike the rule side — where the runtime's `candidates_sound` absorbs the
`HashMap` reasoning — `types` is built by a `HashMap` fold with no pre-existing
characterisation, so it needs its own fold invariant over
`Std.HashMap.getD_insert`. -/

/-- The type table's fold only ever stores the `t` of a `(: (sym s) t)`
declaration, so a safe atom list yields a safe table.  Stated over an arbitrary
starting map so it composes. -/
theorem typesFold_safe :
    ∀ (atoms : List Atom), StateOpFreeList atoms →
      ∀ (m : Std.HashMap String (List Atom)),
        (∀ s t, t ∈ m.getD s [] → StateOpFree t) →
        ∀ s t, t ∈ (atoms.foldl (fun (m : Std.HashMap String (List Atom)) x =>
          match x with
          | Atom.expr [Atom.sym ":", Atom.sym s, ty] => m.insert s (m.getD s [] ++ [ty])
          | _ => m) m).getD s [] → StateOpFree t := by
  intro atoms
  induction atoms with
  | nil => intro _ m hm s t ht; exact hm s t ht
  | cons a rest ih =>
      intro hatoms m hm s t ht
      refine ih hatoms.2 _ ?_ s t ht
      intro s' t' ht'
      simp only at ht'
      split at ht'
      · rename_i s0 ty
        by_cases hk : s' = s0
        · subst hk
          simp only [Std.HashMap.getD_insert_self] at ht'
          rcases List.mem_append.mp ht' with h | h
          · exact hm s' t' h
          · rcases List.mem_singleton.mp h with rfl
            exact hatoms.1.2.2.2.1
        · rw [Std.HashMap.getD_insert,
            if_neg (fun h => hk (beq_iff_eq.mp h).symm)] at ht'
          exact hm s' t' ht'
      · exact hm s' t' ht'

/-- **The `types` table of a derived environment is safe.** -/
theorem ofAtomsGT_types_safe {atoms : List Atom} {gt : GroundingTable}
    (hatoms : StateOpFreeList atoms) :
    ∀ s t, t ∈ (MinEnv.ofAtomsGT atoms gt).types.getD s [] → StateOpFree t := by
  intro s t ht
  exact typesFold_safe atoms hatoms Std.HashMap.emptyWithCapacity
    (by intro s' t' h'; simp at h') s t ht

/-- **The `exprTypes` table of a derived environment is safe.**  It is a plain
`filterMap`, so no fold invariant is needed. -/
theorem ofAtomsGT_exprTypes_safe {atoms : List Atom} {gt : GroundingTable}
    (hatoms : StateOpFreeList atoms) :
    ∀ p ∈ (MinEnv.ofAtomsGT atoms gt).exprTypes, StateOpFree p.1 ∧ StateOpFree p.2 := by
  intro p hp
  obtain ⟨a, hmem, hEq⟩ := List.mem_filterMap.mp hp
  have hsafe : StateOpFree a := stateOpFree_of_mem hatoms hmem
  split at hEq
  · simp only [Option.some.injEq] at hEq
    subst hEq
    exact ⟨hsafe.2.2.1, hsafe.2.2.2.1⟩
  · simp at hEq

/-! ### Capture-avoiding type freshening

Type inference gives each candidate private variable names before matching.
Renaming variables cannot introduce a control symbol, so freshening is inert
for the fragment — the runtime side of that is already proved as
`stateOpFree_renameAllVars`. -/

/-- Freshening one type candidate stays in the fragment. -/
theorem freshenTypeCandidate_safe (avoid : List VarName) (position : Nat)
    {type : Atom} (h : StateOpFree type) :
    StateOpFree (freshenTypeCandidate avoid position type) := by
  rw [freshenTypeCandidate]
  exact stateOpFree_renameAllVars _ h

/-- Freshening a whole argument-type row stays in the fragment.  The avoid set
grows as the row is walked, which changes the NAMES chosen but not their
inertness, so the induction is on the row alone. -/
theorem freshenArgumentTypes_safe :
    ∀ (avoid : List VarName) (position : Nat) (types : List Atom),
      (∀ t ∈ types, StateOpFree t) →
      ∀ t ∈ freshenArgumentTypes avoid position types, StateOpFree t := by
  intro avoid position types
  induction types generalizing avoid position with
  | nil => intro _ t ht; simp [freshenArgumentTypes] at ht
  | cons ty rest ih =>
      intro htypes t ht
      rw [freshenArgumentTypes] at ht
      rcases List.mem_cons.mp ht with rfl | htail
      · exact freshenTypeCandidate_safe avoid position (htypes ty (by simp))
      · exact ih _ _ (fun s hs => htypes s (by simp [hs])) t htail

/-! ### Type matching keeps bindings in the fragment

`matchReduced` bottoms out in `matchAtoms` merged into the threaded type
bindings — exactly the pipeline `MatcherProvenance` characterises — so type
matching cannot introduce a control symbol into the binding state. -/

/-- **Reduced type matching preserves binding safety.** -/
theorem matchReduced_safe (tb : Bindings) (expected actual : Atom) :
    BindingsSafe StateOpFree tb → StateOpFree expected → StateOpFree actual →
    ∀ tb', matchReduced tb expected actual = some tb' →
      BindingsSafe StateOpFree tb' := by
  induction tb, expected, actual using matchReduced.induct
    (motive_2 := fun tb es acts =>
      BindingsSafe StateOpFree tb → (∀ e ∈ es, StateOpFree e) →
      (∀ a ∈ acts, StateOpFree a) → ∀ tb',
        matchReducedList tb es acts = some tb' → BindingsSafe StateOpFree tb') with
  | case1 t tb actual hu =>
      exact fun htb _ _ tb' heq => by
        unfold matchReduced at heq
        rw [if_pos hu] at heq
        cases heq; exact htb
  | case2 tb es acts hu ih =>
      exact fun htb he ha tb' heq => by
        simp only [matchReduced, hu, if_false, Bool.false_eq_true] at heq
        exact ih htb (fun e hm => stateOpFree_of_mem he.2 hm)
          (fun a hm => stateOpFree_of_mem ha.2 hm) tb' heq
  | case3 t tb actual hu hne =>
      exact fun htb he ha tb' heq => by
        simp only [matchReduced, hu, if_false, Bool.false_eq_true] at heq
        have hmem := List.mem_of_head? heq
        obtain ⟨c, hc, hmerge⟩ := List.mem_flatMap.mp (List.mem_filter.mp hmem).1
        exact merge_safe stateOpFree_atomSafety htb
          (matchAtoms_safe stateOpFree_atomSafety
            he ha c hc) tb' hmerge
  | case4 tb =>
      rename_i htb _ _ tb' heq
      simp only [matchReducedList] at heq
      cases heq; exact htb
  | case5 tb e es a acts tbm hstep ih1 ih2 =>
      rename_i htb he ha tb' heq
      simp only [matchReducedList, hstep] at heq
      exact ih2 (ih1 htb (he e (by simp)) (ha a (by simp)) tbm hstep)
        (fun x hx => he x (by simp [hx])) (fun x hx => ha x (by simp [hx])) tb' heq
  | case6 tb e es a acts hstep _ =>
      rename_i tb' heq
      simp only [matchReducedList, hstep] at heq
      exact absurd heq (by simp)
  | case7 t tb x h1 h2 =>
      rename_i tb' heq
      rw [matchReducedList.eq_def] at heq
      split at heq
      · exact (h1 rfl rfl).elim
      · exact (h2 _ _ _ _ rfl rfl).elim
      · exact absurd heq (by simp)

/-- **`matchType` preserves binding safety.**  Its gradual-typing short circuit
returns the incoming bindings untouched. -/
theorem matchType_safe {tb : Bindings} {expected actual : Atom}
    (htb : BindingsSafe StateOpFree tb) (he : StateOpFree expected)
    (ha : StateOpFree actual) :
    ∀ tb', matchType tb expected actual = some tb' →
      BindingsSafe StateOpFree tb' := by
  intro tb' heq
  unfold matchType at heq
  split at heq
  · cases heq; exact htb
  · exact matchReduced_safe tb expected actual htb he ha tb' heq

/-- **Application-argument type matching preserves binding safety**, threading
left to right across the argument row. -/
theorem matchApplicationTypeArguments_safe :
    ∀ (tb : Bindings) (expecteds actuals : List Atom),
      BindingsSafe StateOpFree tb → (∀ e ∈ expecteds, StateOpFree e) →
      (∀ a ∈ actuals, StateOpFree a) →
      ∀ tb', matchApplicationTypeArguments tb expecteds actuals = some tb' →
        BindingsSafe StateOpFree tb' := by
  intro tb expecteds
  induction expecteds generalizing tb with
  | nil =>
      intro actuals htb _ _ tb' heq
      cases actuals with
      | nil => rw [matchApplicationTypeArguments] at heq; cases heq; exact htb
      | cons _ _ => rw [matchApplicationTypeArguments.eq_def] at heq; simp at heq
  | cons e es ih =>
      intro actuals htb he ha tb' heq
      cases actuals with
      | nil => rw [matchApplicationTypeArguments.eq_def] at heq; simp at heq
      | cons a acts =>
          rw [matchApplicationTypeArguments] at heq
          cases hstep : matchType tb e a with
          | none => rw [hstep] at heq; simp at heq
          | some tbm =>
              rw [hstep] at heq
              exact ih tbm acts
                (matchType_safe htb (he e (by simp)) (ha a (by simp)) tbm hstep)
                (fun x hx => he x (by simp [hx])) (fun x hx => ha x (by simp [hx]))
                tb' heq

/-- Type inference enumerates every ordered combination of declared argument
types.  A row drawn from that enumeration only ever contains elements of the
underlying lists, so safety of the sources transfers to every row. -/
theorem cartesian_mem_safe {P : Atom → Prop} :
    ∀ (lists : List (List Atom)), (∀ l ∈ lists, ∀ x ∈ l, P x) →
      ∀ row ∈ cartesian lists, ∀ x ∈ row, P x := by
  intro lists
  induction lists with
  | nil =>
      intro _ row hrow x hx
      rw [cartesian] at hrow
      rcases List.mem_singleton.mp hrow with rfl
      cases hx
  | cons l rest ih =>
      intro hl row hrow x hx
      rw [cartesian] at hrow
      obtain ⟨a, ha, hrow'⟩ := List.mem_flatMap.mp hrow
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hrow'
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hl l (by simp) x ha
      · exact ih (fun m hm => hl m (by simp [hm])) t ht x hx'

/-- The gradual fallback is safe when an arrow has no return component;
otherwise its selected last component inherits safety from the arrow list. -/
theorem getLastD_stateOpFree (types : List Atom)
    (safe : ∀ type ∈ types, StateOpFree type) :
    StateOpFree ((types.getLast?).getD (.sym "%Undefined%")) := by
  cases types with
  | nil => simp [worldMutatingHeads]
  | cons head tail =>
      rw [List.getLast?_eq_some_getLast (by simp)]
      simp only [Option.getD_some]
      exact safe _ (List.getLast_mem (by simp))

/-- Head-selection companion used by the `StateValue` type rule. -/
theorem getHeadD_stateOpFree (types : List Atom)
    (safe : ∀ type ∈ types, StateOpFree type) :
    StateOpFree (types.head?.getD (.sym "%Undefined%")) := by
  cases types with
  | nil => simp [worldMutatingHeads]
  | cons head tail =>
      simp only [List.head?_cons, Option.getD_some]
      exact safe head (by simp)

/-- Every successful inferred application result is safe when the freshened
function candidates and each prepared Cartesian argument row are safe.  This
is the stable membership boundary for the hard expression cases of
`getTypes`; the recursive lookup proof need not reopen the unifier. -/
theorem inferredType_member_stateOpFree
    {functionTypes : List Atom}
    {actualTypeChoices : List (List Atom)} {result : Atom}
    (prepareActuals : List Atom → List Atom)
    (functionsSafe : ∀ type ∈ functionTypes, StateOpFree type)
    (actualsSafe : ∀ actualTypes ∈ actualTypeChoices,
      ∀ type ∈ prepareActuals actualTypes, StateOpFree type)
    (member : result ∈
      functionTypes.flatMap (fun type =>
        actualTypeChoices.filterMap (fun actualTypes =>
          match type with
          | .expr (.sym "->" :: types) =>
              match types.getLast? with
              | none => none
              | some returnType =>
                  match matchApplicationTypeArguments [] types.dropLast
                      (prepareActuals actualTypes) with
                  | some bindings => some (instantiate bindings returnType)
                  | none => none
          | _ => none))) :
    StateOpFree result := by
  obtain ⟨functionType, functionMember, functionResult⟩ :=
    List.mem_flatMap.mp member
  obtain ⟨actualTypes, actualTypesMember, resultEquation⟩ :=
    List.mem_filterMap.mp functionResult
  cases functionType with
  | sym name => simp at resultEquation
  | var name => simp at resultEquation
  | gnd value => simp at resultEquation
  | expr functionAtoms =>
      cases functionAtoms with
      | nil => simp at resultEquation
      | cons functionHead types =>
          cases functionHead with
          | var name => simp at resultEquation
          | gnd value => simp at resultEquation
          | expr atoms => simp at resultEquation
          | sym name =>
              by_cases arrow : name = "->"
              · subst name
                cases last : types.getLast? with
                | none => simp [last] at resultEquation
                | some returnType =>
                    generalize matchedEquation :
                      matchApplicationTypeArguments [] types.dropLast
                        (prepareActuals actualTypes) = matched
                        at resultEquation
                    cases matched with
                    | none => simp [last, matchedEquation] at resultEquation
                    | some bindings =>
                        have outputEquation : instantiate bindings returnType =
                            result := by
                          simpa [last, matchedEquation] using resultEquation
                        have functionSafe :=
                          functionsSafe _ functionMember
                        have typesSafe : ∀ type ∈ types,
                            StateOpFree type := by
                          intro type typeMember
                          exact stateOpFree_of_mem functionSafe.2
                            (by simp [typeMember])
                        have bindingsSafe : BindingsSafe StateOpFree bindings :=
                          matchApplicationTypeArguments_safe [] types.dropLast
                            (prepareActuals actualTypes) (by
                              simp [BindingsSafe])
                            (fun type typeMember => typesSafe type
                              (List.mem_of_mem_dropLast typeMember))
                            (actualsSafe actualTypes actualTypesMember)
                            bindings matchedEquation
                        rw [← outputEquation]
                        exact StateFreePreservation.stateOpFree_instantiate
                          ((bindingsSafe_stateOpFree_iff bindings).mp
                            bindingsSafe)
                          returnType
                          (typesSafe returnType
                            (List.mem_of_getLast? last))
              · simp [arrow] at resultEquation

/-- Erasing the proof payload after filtering an attached list is ordinary
filtering.  Functional induction on `getTypes` exposes the attached form of
the direct expression-type lookup, so this small boundary equation keeps that
implementation detail out of the safety cases. -/
private theorem unattach_filter_attachWith_stateFree
    {α : Type} {property : α → Prop} (entries : List α)
    (all : ∀ entry ∈ entries, property entry) (predicate : α → Bool) :
    ((entries.attachWith property all).filter
      (fun entry => predicate entry.1)).unattach =
      entries.filter predicate := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases headSelected : predicate head = true
      · simp only [List.attachWith, List.pmap, List.filter,
          List.unattach, headSelected]
        apply congrArg (List.cons head)
        exact inductionHypothesis (fun entry entryMember =>
          all entry (List.mem_cons_of_mem _ entryMember))
      · simp only [List.attachWith, List.pmap, List.filter,
          List.unattach, headSelected]
        exact inductionHypothesis (fun entry entryMember =>
          all entry (List.mem_cons_of_mem _ entryMember))

private theorem unattach_filter_attach_stateFree
    {α : Type} (entries : List α) (predicate : α → Bool) :
    (entries.attach.filter (fun entry => predicate entry.1)).unattach =
      entries.filter predicate := by
  exact unattach_filter_attachWith_stateFree entries (fun _ member => member)
    predicate

/-- Recursive type lookup preserves the state-free fragment whenever the two
precomputed declaration indexes do.  The expression-inference cases consume
`inferredType_member_stateOpFree`; the runtime's generated induction principle
keeps its recursive Cartesian implementation confined to this boundary. -/
theorem getTypes_stateOpFree
    {env : MinEnv}
    (typesSafe : ∀ symbol type,
      type ∈ env.types.getD symbol [] → StateOpFree type)
    (expressionTypesSafe : ∀ entry ∈ env.exprTypes,
      StateOpFree entry.1 ∧ StateOpFree entry.2) :
    ∀ atom, StateOpFree atom →
      ∀ type ∈ getTypes env atom, StateOpFree type := by
  intro atom
  induction atom using Metta.Minimal.getTypes.induct env <;>
    intro atomSafe type member
  case case1 value =>
    rw [Metta.Minimal.getTypes.eq_1] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case2 value =>
    rw [Metta.Minimal.getTypes.eq_2] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case3 value =>
    rw [Metta.Minimal.getTypes.eq_3] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case4 value =>
    rw [Metta.Minimal.getTypes.eq_4] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case5 typeName payload =>
    rw [Metta.Minimal.getTypes.eq_5] at member
    simp at member
    subst type
    simpa [StateOpFree] using atomSafe
  case case6 ground hInt hFloat hString hBool hExternal =>
    rw [Metta.Minimal.getTypes.eq_6 env ground hInt hFloat hString hBool
      hExternal] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case7 name =>
    rw [Metta.Minimal.getTypes.eq_7] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case8 symbol empty =>
    rw [Metta.Minimal.getTypes.eq_8, empty] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]
  case case9 symbol nonempty =>
    rw [Metta.Minimal.getTypes.eq_8] at member
    split at member
    next empty => exact (nonempty empty).elim
    next => exact typesSafe symbol type member
  case case10 value inductionHypothesis =>
    rw [Metta.Minimal.getTypes.eq_9] at member
    simp at member
    subst type
    apply stateOpFree_expr_iff_list.mpr
    refine ⟨by simp [StateOpFree, worldMutatingHeads], ?_⟩
    refine ⟨getHeadD_stateOpFree (getTypes env value) ?_, trivial⟩
    intro valueType valueTypeMember
    have valueSafe : StateOpFree value :=
      stateOpFree_of_mem atomSafe.2 (by simp)
    exact inductionHypothesis valueSafe valueType valueTypeMember
  case case11 head arguments notState first rest query =>
    have query' : env.exprTypes.filter (fun entry =>
        entry.1 == .expr (head :: arguments)) = first :: rest := by
      rw [unattach_filter_attach_stateFree env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at query
      exact query
    have indexed : type ∈
        (env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments))).map (·.2) := by
      rw [Metta.Minimal.getTypes.eq_10 env head arguments notState,
        query'] at member
      simp only at member
      rw [query']
      exact member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp indexed
    exact (expressionTypesSafe entry (List.mem_filter.mp entryMember).1).2
  case case12 head arguments notState query _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have query' : env.exprTypes.filter (fun entry =>
        entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach_stateFree env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at query
      exact query
    have inferredMember := member
    rw [Metta.Minimal.getTypes.eq_10 env head arguments notState,
      query'] at inferredMember
    simp only at inferredMember
    split at inferredMember
    next =>
      have typeEquation : type = .sym "%Undefined%" := by
        simpa using inferredMember
      subst type
      simp [StateOpFree, worldMutatingHeads]
    next =>
      have headSafe : StateOpFree head :=
        stateOpFree_of_mem atomSafe.2 (by simp)
      have argumentsSafe : ∀ argument ∈ arguments,
          StateOpFree argument := by
        intro argument argumentMember
        exact stateOpFree_of_mem atomSafe.2 (by simp [argumentMember])
      refine inferredType_member_stateOpFree
        (fun rawTypes => freshenArgumentTypes _ 0 rawTypes) ?_ ?_
        inferredMember
      · intro functionType functionMember
        obtain ⟨rawType, rawMember, rfl⟩ :=
          List.mem_map.mp functionMember
        exact freshenTypeCandidate_safe _ _
          (ihHead headSafe rawType rawMember)
      · intro rawTypes rawTypesMember
        apply freshenArgumentTypes_safe
        exact cartesian_mem_safe (lists := arguments.map (getTypes env))
          (by
            intro candidates candidatesMember candidate candidateMember
            obtain ⟨argument, argumentMember, rfl⟩ :=
              List.mem_map.mp candidatesMember
            exact ihArguments argument argumentMember
              (argumentsSafe argument argumentMember) candidate
              candidateMember)
          rawTypes rawTypesMember
  case case13 head arguments notState query _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have query' : env.exprTypes.filter (fun entry =>
        entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach_stateFree env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at query
      exact query
    have inferredMember := member
    rw [Metta.Minimal.getTypes.eq_10 env head arguments notState,
      query'] at inferredMember
    simp only at inferredMember
    split at inferredMember
    next =>
      have typeEquation : type = .sym "%Undefined%" := by
        simpa using inferredMember
      subst type
      simp [StateOpFree, worldMutatingHeads]
    next =>
      have headSafe : StateOpFree head :=
        stateOpFree_of_mem atomSafe.2 (by simp)
      have argumentsSafe : ∀ argument ∈ arguments,
          StateOpFree argument := by
        intro argument argumentMember
        exact stateOpFree_of_mem atomSafe.2 (by simp [argumentMember])
      refine inferredType_member_stateOpFree
        (fun rawTypes => freshenArgumentTypes _ 0 rawTypes) ?_ ?_
        inferredMember
      · intro functionType functionMember
        obtain ⟨rawType, rawMember, rfl⟩ :=
          List.mem_map.mp functionMember
        exact freshenTypeCandidate_safe _ _
          (ihHead headSafe rawType rawMember)
      · intro rawTypes rawTypesMember
        apply freshenArgumentTypes_safe
        exact cartesian_mem_safe (lists := arguments.map (getTypes env))
          (by
            intro candidates candidatesMember candidate candidateMember
            obtain ⟨argument, argumentMember, rfl⟩ :=
              List.mem_map.mp candidatesMember
            exact ihArguments argument argumentMember
              (argumentsSafe argument argumentMember) candidate
              candidateMember)
          rawTypes rawTypesMember
  case case14 =>
    rw [Metta.Minimal.getTypes.eq_11] at member
    simp at member
    subst type
    simp [StateOpFree, worldMutatingHeads]

/-- The derived environment closes recursive type lookup over every safe atom. -/
theorem ofAtomsGT_getTypes_safe {atoms : List Atom} {gt : GroundingTable}
    (atomsSafe : StateOpFreeList atoms) :
    ∀ atom, StateOpFree atom → ∀ type,
      type ∈ getTypes (MinEnv.ofAtomsGT atoms gt) atom → StateOpFree type :=
  getTypes_stateOpFree (ofAtomsGT_types_safe atomsSafe)
    (ofAtomsGT_exprTypes_safe atomsSafe)

/-! ## Negative control

The workers preserve the world, but the interpreter as a whole does NOT — the
mutating arms are real.  Re-exporting the existing mutation witness here keeps
the two facts adjacent, so a later reader cannot mistake "the workers are
pure" for "the interpreter is pure". -/

/-- Regression: a mutating step still writes the world, so the unconditional
worker lemmas above have not accidentally proved too much. -/
theorem mutation_still_writes (fuel : Nat) :
    (interpretStack1 StateFreeExecution.fullPreludeEnv fuel St.init
      StateFreeExecution.mutatingItem).2.world.selfExtra = [Atom.sym "A"] :=
  StateFreeExecution.mutatingItem_step_writes_world fuel

/-! ## A nontrivial whole-run certificate

The generic certificate API in `StateFreeExecution` is useful only if it can
certify a pending evaluator step, not merely a finished scheduler frame.
Evaluating a variable performs a real `evalOp`/`queryOp` step; the variable-head
guard returns `NotReducible` without consulting the environment.  The witness
therefore runs in every environment, including the shipped prelude.  Its
invariant enumerates precisely the two reachable items and contains no world
equation, so it does not assume the property proved by the certificate. -/

/-- A pending evaluation whose query takes the variable-head guard. -/
def pendingVariableEvalItem : Item :=
  { stack := [{ atom := Atom.expr [Atom.sym "eval", Atom.var "x"], fin := false }],
    bnd := [] }

/-- The finished item produced because variable-headed queries do not reduce. -/
def pendingEvalFinishedItem : Item :=
  finItem [] notReducibleA []

/-- The pending evaluator takes one genuine query step to the finished
`NotReducible` item. -/
theorem pendingVariableEvalItem_step (env : MinEnv) (fuel : Nat) (st : St) :
    interpretStack1 env fuel st pendingVariableEvalItem =
      ([pendingEvalFinishedItem], st) := by
  simp [interpretStack1, pendingVariableEvalItem, pendingEvalFinishedItem,
    evalOp, queryOp, Metta.instantiate_nil,
    Metta.Minimal.isEmbeddedOp, Metta.Minimal.isVariableHeaded]

/-- The finished successor is a fixed point of one interpreter step. -/
theorem pendingEvalFinishedItem_step (env : MinEnv) (fuel : Nat) (st : St) :
    interpretStack1 env fuel st pendingEvalFinishedItem =
      ([pendingEvalFinishedItem], st) := by
  simp [interpretStack1, pendingEvalFinishedItem, finItem]

/-- Exactly the two configurations reachable in the pending variable
run.  The world parameter is intentionally ignored: preservation is proved,
not stored in the invariant. -/
def PendingVariableEvalInv (_ : World) (item : Item) : Prop :=
  item = pendingVariableEvalItem ∨ item = pendingEvalFinishedItem

/-- A genuine pending evaluator run has a derivation-local state-free
certificate.  Its first arm performs evaluation and query; its second arm is
the resulting finished frame. -/
theorem pendingVariableEval_stateFreeExecution (env : MinEnv) :
    StateFreeExecution.Certificate env PendingVariableEvalInv where
  preserves := by
    intro fuel st item reached
    rcases reached with rfl | rfl
    · rw [pendingVariableEvalItem_step]
    · apply StateFreeExecution.interpretStack1_preservesWorld_of_fin
        env fuel st pendingEvalFinishedItem
        { atom := notReducibleA, fin := true } []
      · rfl
      · rfl
  reached := by
    intro fuel st item reached successor member
    rcases reached with rfl | rfl
    · rw [pendingVariableEvalItem_step] at member
      have successorEquation : successor = pendingEvalFinishedItem := by
        simpa using member
      exact Or.inr successorEquation
    · rw [pendingEvalFinishedItem_step] at member
      have successorEquation : successor = pendingEvalFinishedItem := by
        simpa using member
      exact Or.inr successorEquation

/-- The complete pending evaluation preserves the world for every fuel and
every initial state, in the full prelude environment. -/
theorem fullPrelude_pendingVariableEval_preservesWorld
    (fuel : Nat) (st : St) :
    (interpretFuel StateFreeExecution.fullPreludeEnv fuel st
      [pendingVariableEvalItem] []).2.world =
      st.world := by
  apply StateFreeExecution.interpretFuel_preservesWorld
    (pendingVariableEval_stateFreeExecution StateFreeExecution.fullPreludeEnv)
  intro item member
  have itemEquation : item = pendingVariableEvalItem := by simpa using member
  exact Or.inl itemEquation

end Mettapedia.Languages.MeTTa.HE.StateFreeInterpreterSteps
