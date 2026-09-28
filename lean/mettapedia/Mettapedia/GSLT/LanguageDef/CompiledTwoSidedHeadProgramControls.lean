import Mettapedia.GSLT.LanguageDef.CompiledHeadCodeTree

/-!
# Controls for compiled two-sided equation heads

Concrete runs of `CompiledTwoSidedHeadProgram`, each checked against the
defunctionalized machine's activation step (`sourceActivation`) on the same
query.  Query variables are `0, 1, ...`; the fresh supply starts at `10`.

* `occursCheck_compiled`, `occursCheck_source`: the head `(X, (f X))` against
  the query `($0, $0)` fails in both.  The compiled code binds `$0` to a node
  `(f $10)` and loads `$10` as the child; the repeated occurrence of `X` then
  unifies `(f $10)` with `$10`, which the occurs check refutes.
* `repeated_compiled`, `repeated_source`: the head `(X, X)` against `(a, $1)`
  binds the query variable `$1` to `a`.
* `nested_compiled`, `nested_source`: the head `((g X Y), X, Y)` against
  `($0, a, b)` binds `$0` to `(g a b)`: the query variable becomes a node of
  fresh variables, which the later occurrences of `X` and `Y` fill.
* `constant_compiled`, `constant_source`: the head `(a)` binds the query
  variable `$0` to `a`; `constantClash_compiled`, `constantClash_source`: it
  rejects `(b)`.
* Negative control: `forgetRepeats` compiles every occurrence of a slot as a
  first occurrence, the reading of a head as a linear one-sided pattern.  It
  accepts `(X, X)` against `(a, b)` (`forgetRepeats_accepts`), which the
  emitted code and the source activation both reject (`repeatedClash_compiled`,
  `repeatedClash_source`): the compile-time split between `bindSlot` and
  `equateSlot` carries the head's equality constraints.

`entry_controls` shows every query here satisfies the activation theorems'
entry condition, so `activation_exact` covers each of them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram.Controls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

/-- Two function symbols, of arities one and two. -/
inductive Fn where
  | f
  | g
  deriving DecidableEq

/-- The arity of a function symbol. -/
def Fn.arity : Fn → ℕ
  | .f => 1
  | .g => 2

/-- String constants, natural-number variables, `f` and `g`. -/
abbrev sig : LPSignature.{0, 0, 0, 0} where
  constants := String
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Fn
  functionArity := Fn.arity

/-- No primitives: the activation step never calls them. -/
def noPrim : Empty → List (Term sig) → Subst sig × ℕ → Option (Term sig) :=
  fun op => op.elim

/-- No tests: the activation step never calls them. -/
def noTest : Empty → List (Term sig) → Subst sig × ℕ → Option Bool :=
  fun op => op.elim

/-! ## Evaluating the unifier on one pair -/

theorem unifyTotal_var_const (v : ℕ) (c : String) :
    unifyTotal [(Term.var (σ := sig) v, Term.const c)] =
      some (Subst.id sig ∘ₛ Subst.single v (.const c)) := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp [Term.occursIn, Subst.applyEqs]
  rw [unifyTotal.eq_def (σ := sig)]

theorem unifyTotal_const_var (c : String) (v : ℕ) :
    unifyTotal [(Term.const (σ := sig) c, Term.var v)] =
      some (Subst.id sig ∘ₛ Subst.single v (.const c)) := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp [Subst.applyEqs]
  rw [unifyTotal.eq_def (σ := sig)]

theorem unifyTotal_const_const {c d : String} (different : c ≠ d) :
    unifyTotal [(Term.const (σ := sig) c, Term.const d)] = none := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp [different]

theorem unifyTotal_var_var {v w : ℕ} (different : v ≠ w) :
    unifyTotal [(Term.var (σ := sig) v, Term.var w)] =
      some (Subst.id sig ∘ₛ Subst.single v (.var w)) := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp [different, Subst.applyEqs]
  rw [unifyTotal.eq_def (σ := sig)]

theorem unifyTotal_app_var_occurs {function : Fn}
    {children : Fin (Fn.arity function) → Term sig} {v : ℕ}
    (occurs : (Term.app (σ := sig) function children).occursIn v = true) :
    unifyTotal [(Term.app (σ := sig) function children, Term.var v)] = none := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp only [occurs, if_true]

theorem unifyTotal_app_var {function : Fn} {children : Fin (Fn.arity function) → Term sig}
    {v : ℕ} (notOccurs : (Term.app (σ := sig) function children).occursIn v = false) :
    unifyTotal [(Term.app (σ := sig) function children, Term.var v)] =
      some (Subst.id sig ∘ₛ Subst.single v (.app function children)) := by
  rw [unifyTotal.eq_def (σ := sig)]
  simp only [notOccurs, Bool.false_eq_true, if_false, Subst.applyEqs, List.map_nil]
  rw [unifyTotal.eq_def (σ := sig)]

/-! ## The entry condition -/

/-- Queries over variables below `10`, with the empty store and the supply at
`10`, satisfy the entry condition. -/
theorem entry_query (args : List (Term sig))
    (below : ∀ arg ∈ args, ∀ v : ℕ, v ∈ arg.freeVars → v < 10) :
    EntryCondition id (Subst.id sig) 10 args where
  idempotent _ := rfl
  store v := ⟨fun _ => rfl, fun notIn x member => by
    rw [Subst.id_apply, Term.mem_freeVars_var (σ := sig)] at member
    subst member
    exact notIn⟩
  args arg member v occurs inSupply := by
    obtain ⟨m, bound, rfl⟩ := inSupply
    have : m < 10 := below arg member m occurs
    omega

/-- The queries of these controls satisfy the entry condition. -/
theorem entry_controls :
    ∀ args ∈ ([[.var 0, .var 0], [.const "a", .var 1], [.var 0, .const "a", .const "b"],
        [.var 0], [.const "b"], [.const "a", .const "b"]] : List (List (Term sig))),
      EntryCondition id (Subst.id sig) 10 args := by
  intro args member
  refine entry_query args fun arg memberArg v occurs => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at memberArg <;>
    rcases memberArg with rfl | rfl | rfl <;>
    simp_all [Term.mem_freeVars_var (σ := sig), Term.not_mem_freeVars_const (σ := sig)]

/-! ## Occurs check -/

/-- `(X, (f X))`. -/
def headOccurs : List (HeadPattern sig (Fin 1)) := [.var 0, .app Fn.f fun _ => .var 0]

theorem headOccurs_code :
    emitHead headOccurs = [.bindSlot 0 0, .node 1 .f 2, .equateSlot 2 0] := rfl

theorem occursCheck_compiled :
    compiledActivation id headOccurs [.var 0, .var 0] (Subst.id sig) 10 = none := by
  unfold compiledActivation
  rw [headOccurs_code]
  simp [headOccurs, exec, step, initialState, bindFreshNode, freshVariables, loadChildren,
    Subst.single, Fn.arity]
  rw [unifyTotal.eq_def (σ := sig)]
  simp only [Term.occursIn, List.any_eq_true, List.mem_finRange, true_and]
  rw [if_pos ⟨⟨0, by decide⟩, by simp [freshVariables, Term.occursIn]⟩]

theorem occursCheck_source :
    sourceActivation id noPrim noTest headOccurs [.var 0, .var 0] (Subst.id sig) 10 = none := by
  unfold sourceActivation
  simp [headOccurs, substitutionStore, unifyAll, instArgs, headTemplates, freshVariables,
    instantiate, unifyTotal_var_var]
  apply unifyTotal_app_var_occurs
  simp only [Term.occursIn]
  exact List.any_eq_true.mpr ⟨⟨0, by decide⟩, List.mem_finRange _, by simp [Subst.single, Term.occursIn]⟩

/-! ## A repeated head variable binds a query variable -/

/-- `(X, X)`. -/
def headSame : List (HeadPattern sig (Fin 1)) := [.var 0, .var 0]

theorem headSame_code : emitHead headSame = [.bindSlot 0 0, .equateSlot 1 0] := rfl

theorem repeated_compiled :
    (compiledActivation id headSame [.const "a", .var 1] (Subst.id sig) 10).map
      (fun result => result.2.1 1) = some (.const "a") := by
  unfold compiledActivation
  rw [headSame_code]
  simp [headSame, exec, step, initialState, unifyTotal_const_var, Subst.single]

theorem repeated_source :
    (sourceActivation id noPrim noTest headSame [.const "a", .var 1] (Subst.id sig) 10).map
      (fun result => result.2.1 1) = some (.const "a") := by
  unfold sourceActivation
  simp [headSame, substitutionStore, unifyAll, instArgs, headTemplates, freshVariables,
    instantiate, unifyTotal_var_const, unifyTotal_const_var, Subst.single]

/-! ## A query variable becomes a node whose children the head fills -/

/-- `((g X Y), X, Y)`. -/
def headNested : List (HeadPattern sig (Fin 2)) :=
  [.app Fn.g (fun i => .var i), .var 0, .var 1]

theorem headNested_code : emitHead headNested =
    [.node 0 .g 3, .bindSlot 3 0, .bindSlot 4 1, .equateSlot 1 0, .equateSlot 2 1] := rfl

/-- `(g a b)`. -/
def nodeAB : Term sig := .app Fn.g fun i => if i.val = 0 then .const "a" else .const "b"

theorem nested_compiled :
    (compiledActivation id headNested [.var 0, .const "a", .const "b"] (Subst.id sig) 10).map
      (fun result => result.2.1 0) = some nodeAB := by
  unfold compiledActivation
  rw [headNested_code]
  simp +decide [exec, step, initialState, bindFreshNode, freshVariables, loadChildren,
    Subst.single, unifyTotal_var_const]
  unfold nodeAB
  congr 1
  funext i
  fin_cases i <;> rfl

theorem nested_source :
    (sourceActivation id noPrim noTest headNested [.var 0, .const "a", .const "b"]
      (Subst.id sig) 10).map (fun result => result.2.1 0) = some nodeAB := by
  unfold sourceActivation
  simp [headNested, substitutionStore, unifyAll, instArgs, headTemplates, freshVariables,
    instantiate]
  rw [unifyTotal_app_var (by simp [Term.occursIn]; omega)]
  simp [Subst.single, unifyTotal_var_const]
  unfold nodeAB
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## Constants -/

/-- `(a)`. -/
def headConst : List (HeadPattern sig (Fin 0)) := [.const "a"]

theorem headConst_code : emitHead headConst = [.constant 0 "a"] := rfl

theorem constant_compiled :
    (compiledActivation id headConst [.var 0] (Subst.id sig) 10).map
      (fun result => result.2.1 0) = some (.const "a") := by
  unfold compiledActivation
  rw [headConst_code]
  simp [headConst, exec, step, initialState, Subst.single]

theorem constant_source :
    (sourceActivation id noPrim noTest headConst [.var 0] (Subst.id sig) 10).map
      (fun result => result.2.1 0) = some (.const "a") := by
  unfold sourceActivation
  simp [headConst, substitutionStore, unifyAll, instArgs, headTemplates, instantiate,
    unifyTotal_const_var, Subst.single]

theorem constantClash_compiled :
    compiledActivation id headConst [.const "b"] (Subst.id sig) 10 = none := by
  unfold compiledActivation
  rw [headConst_code]
  simp [headConst, exec, step, initialState]

theorem constantClash_source :
    sourceActivation id noPrim noTest headConst [.const "b"] (Subst.id sig) 10 = none := by
  unfold sourceActivation
  simp [headConst, substitutionStore, unifyAll, instArgs, headTemplates, instantiate,
    unifyTotal_const_const (show "a" ≠ "b" by decide)]

/-! ## Negative control: repeated occurrences read as first occurrences -/

section ForgetRepeats

variable {σ : LPSignature} {Slot : Type}

/-- Compile a repeated occurrence of a slot as a first occurrence. -/
def forgetRepeat : HeadOp σ Slot → HeadOp σ Slot
  | .equateSlot source slot => .bindSlot source slot
  | op => op

/-- The head's code with every occurrence of a slot compiled as a first
occurrence: the reading of a head as a linear one-sided pattern. -/
def forgetRepeats [DecidableEq Slot] (patterns : List (HeadPattern σ Slot)) :
    List (HeadOp σ Slot) :=
  (emitHead patterns).map forgetRepeat

end ForgetRepeats

theorem forgetRepeats_accepts :
    (exec id (forgetRepeats headSame)
      (initialState [.const "a", .const "b"] (Subst.id sig) 10)).isSome = true := by
  simp [forgetRepeats, headSame_code, forgetRepeat, exec, step, initialState]

theorem repeatedClash_compiled :
    compiledActivation id headSame [.const "a", .const "b"] (Subst.id sig) 10 = none := by
  unfold compiledActivation
  rw [headSame_code]
  simp [headSame, exec, step, initialState, unifyTotal_const_const (show "a" ≠ "b" by decide)]

theorem repeatedClash_source :
    sourceActivation id noPrim noTest headSame [.const "a", .const "b"] (Subst.id sig) 10 =
      none := by
  unfold sourceActivation
  simp [headSame, substitutionStore, unifyAll, instArgs, headTemplates, freshVariables,
    instantiate, unifyTotal_var_const, Subst.single,
    unifyTotal_const_const (show "a" ≠ "b" by decide)]

/-! ## The code tree of a relation -/

section CodeTree

open Mettapedia.GSLT.LanguageDef.CompiledHeadCodeTree

/-- An equation of the relation `()` with the head `params` and a failing body. -/
def headEquation {k : ℕ} (params : List (HeadPattern sig (Fin k))) :
    Equation (headTemplates sig) Unit Empty :=
  ⟨k, params, .fail⟩

/-- `(f X)`, `(f a)`, `(g X Y)`, `(f b)`, in this order. -/
def relationHeads : EqProgram (headTemplates sig) Unit Empty :=
  [((), headEquation (k := 1) [.app Fn.f fun _ => .var 0]),
   ((), headEquation (k := 0) [.app Fn.f fun _ => .const "a"]),
   ((), headEquation (k := 2) [.app Fn.g fun i => .var i]),
   ((), headEquation (k := 0) [.app Fn.f fun _ => .const "b"])]

theorem relationHeads_code :
    (relationHeads.equations ()).map headCode =
      [[.node 0 .f 1, .bindSlot 1 0], [.node 0 .f 1, .constant 1 "a"],
       [.node 0 .g 1, .bindSlot 1 0, .bindSlot 2 1], [.node 0 .f 1, .constant 1 "b"]] := by
  decide

/-- The first two heads share their first instruction: nine instructions are
stored as eight. -/
theorem relationHeads_size : (relationTree relationHeads ()).size = 8 := by
  decide

/-- The fourth head starts like the first two but is not adjacent to them:
sharing it would reorder the heads, so it is not shared. -/
theorem relationHeads_shared :
    CodeTree.sharedWithPrevious [] ((relationHeads.equations ()).map headCode) = 1 := by
  decide

/-- The query `(f $0)` activates the first, second and fourth heads, in order;
the third fails at the shared node test. -/
theorem relationHeads_open_query :
    (treeActivate id (relationTree relationHeads ()) [.app Fn.f fun _ => .var 0]
      (Subst.id sig) 10).map Prod.fst = [0, 1, 3] := by
  decide

/-- The query `(f a)` activates the first two heads only. -/
theorem relationHeads_closed_query :
    (treeActivate id (relationTree relationHeads ()) [.app Fn.f fun _ => .const "a"]
      (Subst.id sig) 10).map Prod.fst = [0, 1] := by
  decide

end CodeTree

end Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram.Controls
