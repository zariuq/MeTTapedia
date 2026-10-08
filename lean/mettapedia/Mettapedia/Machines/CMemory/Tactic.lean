import Mettapedia.Machines.CMemory.WP

/-!
# Tactics for C programs: symbolic execution against the weakest precondition

A proof of `CTriple P c Q` with these tactics is symbolic execution.  The
goal is the weakest precondition `c.wp act Q σ`, and the hypotheses about the
state `σ` are the symbolic heap.  Each step applies one rule of `CMemory.WP`
or of the generic calculus; the searches that discharge the rules' premises
apply only the lemmas of `GSLT.Logic.SymbolicHeap` and the atom lemmas
registered here.  Nothing is asserted by a tactic, so the soundness of every
proof is that of the calculus, checked by the kernel.

* `cmem_start σ h`: turn `CTriple P c Q` into the goal `c.wp act Q σ` with
  `h : P σ`.
* `cmem_norm [lemmas]`: the program-structure rules (sequencing, returns,
  conditionals, typed loads, undefined behaviour) as a `simp` set, with
  optional extra lemmas, for instance the equations of an interpreter or a
  decided branch condition.
* `cmem_step [lemmas]`: normalize, then execute the first primitive:
  - a load reads its value from any conjunct of the state (`sep_ensures`);
  - a store splits the whole cell off the state (`sep_split`); the new state
    and its hypothesis keep the names of the ones they replace;
  - a pointer comparison finds both pointers valid or null: from a conjunct,
    or, given `WellFormed σ`, from a held cell of the pointer's block;
  - `malloc` and `realloc` of null run their small axioms with the whole
    state as frame;
  - `free` of null does nothing.
  `free` and `realloc` of a block need the block's specification, through
  `cmem_call` (`free_spec`, `realloc_spec`, `realloc_dynArray`).
* `cmem_vcgen [lemmas]`: `cmem_step` until no rule applies.  What remains is
  a postcondition, a branch (`split_ifs`, `cases`), undefined behaviour, or a
  call to a specified program.
* `cmem_call spec with pats`: call a specified program (`sep_call`),
  normalize the postcondition hypothesis, and take it apart with `rintro pats`.
  A loop written as recursion is proved by induction, and its induction
  hypothesis is called like any other specification.
* `cmem_loop I`: a `Prog.foldList` loop with the invariant `I`
  (`wp_foldList`).
* `cmem_exact`: close a spatial goal `G σ` from a hypothesis about `σ`, up to
  the order and grouping of conjuncts (`sep_entails`).
* `cmem_fact`: close a pure goal from a conjunct of a hypothesis
  (`sep_ensures`), for instance that a null dynamic array is empty.

Side conditions of atom lemmas (bounds of array indices, a field's block and
offset) go to `cmem_side`: `assumption`, then `omega` after the usual
list-length simplifications, then `simp`.

A hypothesis `WellFormed σ` beside the symbolic heap is carried across every
call and store (`StepInvariant`), as `wf` or the name it already had.

## Extending the tactics

A new assertion is registered by `macro_rules` for `sep_ensures_atom` (what a
conjunct guarantees), `sep_split_weaken` (what a footprint may be taken
from), `sep_entails_atom` (final entailments) or `cmem_side`.  What an
extension produces is checked by the kernel like any other proof, so an
extension can make the tactics succeed more often, never prove something
false.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra

/-! ## Side conditions -/

/-- Side conditions of atom lemmas, such as array bounds.  Extend with
`macro_rules`. -/
syntax "cmem_side" : tactic

macro_rules
  | `(tactic| cmem_side) => `(tactic| first
      | assumption
      | omega
      | (simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
          List.length_replicate, List.length_take, List.length_set] at *; omega)
      | (simp at *; done)
      | (simp_all; done))

/-! ## Registration of the C atom lemmas -/

macro_rules
  | `(tactic| sep_persistent) => `(tactic| apply reads_persistent)
macro_rules
  | `(tactic| sep_persistent) => `(tactic| apply validAt_persistent)
macro_rules
  | `(tactic| sep_persistent) => `(tactic| apply heldFrom_persistent)

macro_rules
  | `(tactic| sep_ensures_atom) => `(tactic| with_reducible apply ensures_reads_pointsTo)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_reads_dynArray) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_reads_dynArray_base) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_reads_cells) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) => `(tactic| with_reducible apply ensures_valid_pointsTo)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_heldFrom_pointsTo) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| with_reducible apply ensures_valid_dynArray_base)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_valid_dynArray) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (with_reducible apply ensures_valid_liveBlock) <;> cmem_side)
macro_rules
  | `(tactic| sep_ensures_atom) => `(tactic| with_reducible apply ensures_dynArray_offset)
macro_rules
  | `(tactic| sep_ensures_atom) => `(tactic| with_reducible apply ensures_dynArray_length)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| with_reducible apply ensures_dynArray_none_contents)
macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| with_reducible apply ensures_dynArray_none_capacity)

macro_rules
  | `(tactic| sep_split_weaken) =>
      `(tactic| (apply Splits.weaken (pointsTo_le_pointsToAny _ _); sep_split_struct))

/-! ## Normalization -/

section Syntax

open Lean

/-- Extra lemmas for the normalization `simp` set. -/
def simpLemmas (extra : Array Term) :
    MacroM (Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] ",") := do
  let lemmas ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  return .ofElems (lemmas.map fun l => ⟨l.raw⟩)

end Syntax

/-- The program-structure rules of the calculus as a `simp` set, with optional
extra lemmas. -/
syntax "cmem_norm" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| cmem_norm $[[$extra,*]]?) => do
    let extra ← simpLemmas ((extra.map (·.getElems)).getD #[])
    `(tactic| simp only [wp_bind', wp_bind, wp_pure, wp_ret, wp_ite_apply, wp_dite_apply,
        wp_undefined, wp_free_none, CProg.loadU32, CProg.loadPtr, CProg.loadBool,
        ↓reduceIte, ↓reduceDIte, reduceCtorEq, decide_true, decide_false, Bool.not_true,
        Bool.not_false, true_and, and_true, Bool.false_eq_true, Bool.true_eq_false, false_and,
        and_false, false_or, or_false, ne_eq, not_false_eq_true, not_true_eq_false, and_self,
        $extra,*])

/-- Start a proof of a C triple: the goal becomes the weakest precondition at
the state `σ`, with `h` its hypothesis. -/
macro "cmem_start " σ:ident h:ident : tactic =>
  `(tactic| (apply triple_of_wp; intro $σ:ident $h:ident))

section Meta

open Lean Elab Tactic Meta

/-- The validity goal `ValidOpt σ p` of a comparison: null, a pointer that a
conjunct of a hypothesis about `σ` makes valid, or, given `WellFormed σ`, a
pointer with a held cell at or after it in its block. -/
def validityStep (σ : Expr) (program : Expr) : TacticM Unit := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| exact validOpt_none _))
  catch _ =>
    saved.restore
    discard <| withHypothesisAbout σ m!"cmem_step: the comparison{indentExpr program}\nneeds \
        both pointers valid or null." fun h _ => do
      let saved ← saveState
      try
        evalTactic (← `(tactic| (apply validOpt_some $h; sep_ensures)))
      catch _ =>
        saved.restore
        evalTactic (← `(tactic| (apply validOpt_some_wellFormed (by assumption) $h; sep_ensures)))

/-- The name a new state, or a hypothesis about it, takes: the name of the one
it replaces. -/
def successorName (old : Expr) (default : Name) : MetaM Name :=
  if old.isFVar then old.fvarId!.getUserName else pure default

/-- Execute the first primitive of a weakest-precondition goal. -/
def primitiveStep : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let σ ← wpGoalState goal
  let target ← whnfR (← instantiateMVars (← goal.getType))
  let program := target.getArg! 5
  match program.getAppFn.constName? with
  | some ``CProg.load =>
    discard <| withHypothesisAbout σ m!"cmem_step: the load{indentExpr program}\nneeds a \
        conjunct that reads an initialized value at its address." fun h _ => do
      evalTactic (← `(tactic| (apply wp_load $h; sep_ensures)))
  | some ``CProg.store =>
    let (used, invariant) ← framedCall (← `(store_spec _ _))
      m!"cmem_step: the store{indentExpr program}\nneeds a conjunct that holds the whole cell \
        at its address."
    let state := mkIdent (← successorName σ `σ)
    let hyp := mkIdent (← successorName used `h)
    match invariant with
    | some g =>
      let kept := mkIdent (← successorName g `wf)
      evalTactic (← `(tactic| intro _ $state:ident $hyp:ident $kept:ident))
    | none =>
      evalTactic (← `(tactic| intro _ $state:ident $hyp:ident))
  | some ``CProg.ptrEq =>
    evalTactic (← `(tactic| apply wp_ptrEq))
    validityStep σ program
    validityStep σ program
  | some ``CProg.malloc =>
    discard <| framedCall (← `(malloc_spec _)) m!"cmem_step: the allocation{indentExpr program}"
    evalTactic (← `(tactic| try sep_norm))
  | some ``CProg.realloc =>
    unless (program.getArg! 1).isAppOf ``Option.none do
      throwError "cmem_step: the reallocation{indentExpr program}\nneeds the block's \
        specification: use `cmem_call` with `realloc_spec` or `realloc_dynArray`."
    discard <| framedCall (← `(realloc_null_spec _))
      m!"cmem_step: the allocation{indentExpr program}"
    evalTactic (← `(tactic| try sep_norm))
  | some ``CProg.free =>
    throwError "cmem_step: the deallocation{indentExpr program}\nneeds the block's \
      specification: use `cmem_call` with `free_spec`."
  | _ =>
    throwError "cmem_step: no rule executes{indentExpr program}\nUse `split_ifs` or `cases` \
      for a branch, `cmem_call` for a specified program, or prove the postcondition."

/-- One step of symbolic execution. -/
syntax "cmem_step" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cmem_step $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    evalTactic (← `(tactic| try cmem_norm [$extra,*]))
    primitiveStep
    evalTactic (← `(tactic| try cmem_norm [$extra,*]))

/-- Symbolic execution until no rule applies. -/
syntax "cmem_vcgen" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| cmem_vcgen $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (repeat cmem_step [$extra,*]))

/-- **A loop with an invariant**: for a goal `(Prog.foldList f xs b).wp act Q σ`,
the invariant `I rest b σ` is indexed by the elements still to be processed.
Three goals remain: `invariant` (it holds now), `step` (one iteration keeps it,
a triple), and `post` (it gives the postcondition when nothing is left). -/
macro "cmem_loop " I:term : tactic =>
  `(tactic| refine wp_foldList _ _ $I ?step _ _ ?invariant ?post)

/-- Call a specified program inside the current state, framing the rest, and
normalize the postcondition hypothesis.  With `with` patterns, the result, the
new state and the postcondition are introduced by `rintro`. -/
syntax "cmem_call " term (" with" (ppSpace colGt rintroPat)+)? : tactic

macro_rules
  | `(tactic| cmem_call $spec $[with $pats*]?) =>
    match pats with
    | some pats => `(tactic| (sep_call $spec; try sep_norm; rintro $pats*))
    | none => `(tactic| (sep_call $spec; try sep_norm))

/-- Close a spatial goal `G σ` from a hypothesis about `σ`. -/
elab "cmem_exact" : tactic => withMainContext do
  let target ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  unless target.isApp do throwError "cmem_exact: the goal is not about a state"
  discard <| withHypothesisAbout target.appArg! m!"cmem_exact: the goal must follow from a \
      hypothesis, up to the order and grouping of conjuncts." fun h _ => do
    evalTactic (← `(tactic| sep_exact $h))

/-- Close a pure goal from a conjunct of a hypothesis about some state. -/
elab "cmem_fact" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    unless type.isApp && type.appArg!.isFVar do continue
    unless ← isProp type do continue
    let saved ← saveState
    try
      let h ← Term.exprToSyntax decl.toExpr
      evalTactic (← `(tactic| (refine Ensures.apply (O := fun _ => _) ?_ $h; sep_ensures)))
      return
    catch _ =>
      saved.restore
  throwError "cmem_fact: no conjunct of a hypothesis guarantees the goal"

end Meta

end Mettapedia.Machines.CMemory
