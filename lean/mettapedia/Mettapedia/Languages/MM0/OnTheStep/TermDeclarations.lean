import Mettapedia.Languages.MM0.OnTheStep.ArrowTermDeclarations

/-!
# Files of sort and term declarations: the step accepts exactly what MM0's rules accept

MM0's rules here are `checkAll` and the functions it calls, written by hand after MM0's GSLT definition; no
mechanical link to that definition's files is proved.

The theorem of `SortDeclarations`, for files whose statements are sort declarations and term declarations with
binder groups and dependencies: `term all {x: set} (ph: wff x): wff;`, `term imp: wff > wff > wff;`. The program is
`DeclarationProgram.program`, all twenty rules.

* **Statements** (`Statement`): a sort statement, or a term statement (`TermStatement`): its name, its binder
  groups (`Group`: bound, `{x y: s}`, or regular, `(x _: s d …)`, each with a type `Typ`: a sort and its
  dependencies), its argument types and its return type; each as the tree of the `.mm0` grammar
  (`Statement.tree`).
* **MM0's rules** (`checkGroups`, `checkArrow`, `checkTerm`, `checkAll`), as MM0's GSLT definition has them
  (`term_environment_v1`): a term's name is no term's name; the groups in order: a bound group's sort is declared
  and not `strict` and its type has no dependencies, each of its names is no binder name of the term yet and
  becomes a binder name and a bound variable; a regular group's sort is declared and its dependencies are bound
  variables declared before, each of its names is no binder name yet and becomes one, a blank is skipped; each
  argument type's sort is declared and its dependencies are bound variables; the return type's sort is declared
  and not `pure`, and its dependencies are bound variables. Sorts as in `SortDeclarations.declare`.
* **The theorem** (`accepted_reachable_iff`, `on_the_step`): from the bag of such a file, rewriting of bags with
  the none query reaches a bag holding `accepted` exactly when MM0's rules accept the file; on the step, for every state
  that reads as the file's bag. The invariant (`Phase`): the cursor at the rest of the file; or a term under check,
  with the verdict of the whole signature equal to the verdict of what is left to check from the cursor
  (`InTerm`); or `accepted`. The store holds the sort rows, the term name rows, and the binder rows of every term
  checked, each keyed by its term's name; the rows of earlier terms never meet the term under check, whose name is
  fresh (`binderName_mem`, `boundVar_mem`).
* **Examples from MM0's test files** (`Examples`, CeTTa's `tests/langdef/mm0/term_environment_*.mm0`): the five
  positive files are accepted on the step; the files with a pure target, a redeclared term, a strict sort for a
  bound variable, an unknown dependency, an unknown sort are refused: no run reaches `accepted`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.TermDeclarations

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open NamesOnTheStep (Expr)
open Presentation.Schematic
open Machines (ReadsBag stepSystem listState listState_reads)
open NoneRewriting
open DeclarationProgram
open SortDeclarations (SortStatement fileTree SortEnv lookupSort declare envRows mem_envRows rows_of_mem
  sortName_mem_envRows sortEntry_mem_envRows lookupSort_eq_none_iff lookupSort_of_mem mem_of_lookupSort
  declare_nodup mem_one_add)
open ArrowTermDeclarations (secondOf thirdOf fourthOf isTarget isTarget_iff multiStep_append)

universe uO

/-! ## Statements -/

/-- The tree of a list of identifiers (`ids_more`, `ids_empty`). -/
def idsTree : List Expr → Expr
  | [] => node "ids_empty" []
  | x :: xs => node "ids_more" [x, idsTree xs]

/-- The tree of the names of a regular group, `none` for the blank `_` (`bids_more`, `bids_blank`,
`bids_empty`). -/
def bidsTree : List (Option Expr) → Expr
  | [] => node "bids_empty" []
  | some x :: xs => node "bids_more" [x, bidsTree xs]
  | none :: xs => node "bids_blank" [bidsTree xs]

/-- **A type**: a sort and its dependencies. -/
structure Typ where
  sort : Expr
  deps : List Expr

/-- The tree of a type (`typ_deps`). -/
def Typ.tree (ty : Typ) : Expr := node "typ_deps" [ty.sort, idsTree ty.deps]

/-- **A binder group**: bound, `{x y: s}`, or regular, `(x _: s d …)`. -/
inductive Group where
  | bound (names : List Expr) (ty : Typ)
  | regular (names : List (Option Expr)) (ty : Typ)

/-- The tree of a group (`tbinder_bound`, `tbinder_regular`). -/
def Group.tree : Group → Expr
  | .bound names ty => node "tbinder_bound" [idsTree names, ty.tree]
  | .regular names ty => node "tbinder_regular" [bidsTree names, ty.tree]

/-- The tree of the groups (`tbinders_more`, `tbinders_empty`). -/
def groupsTree : List Group → Expr
  | [] => node "tbinders_empty" []
  | g :: gs => node "tbinders_more" [g.tree, groupsTree gs]

/-- The tree of an arrow type (`arrow_more`, `arrow_last`). -/
def arrowTree : List Typ → Typ → Expr
  | [], r => node "arrow_last" [r.tree]
  | a :: as, r => node "arrow_more" [a.tree, arrowTree as r]

/-- **A term statement**: its name, binder groups, argument types and return type. -/
structure TermStatement where
  name : Expr
  groups : List Group
  args : List Typ
  ret : Typ

/-- The tree of a term statement (`statement_term`). -/
def TermStatement.tree (t : TermStatement) : Expr :=
  node "statement_term" [t.name, groupsTree t.groups, arrowTree t.args t.ret]

/-- **A statement**: a sort declaration or a term declaration. -/
inductive Statement where
  | sort (d : SortStatement)
  | term (t : TermStatement)

/-- The tree of a statement. -/
def Statement.tree : Statement → Expr
  | .sort d => d.tree
  | .term t => t.tree

/-! ## MM0's rules -/

/-- **An environment**: the declared sorts with their modifiers, and the declared term names. -/
structure Env where
  sorts : SortEnv
  terms : List Expr

/-- The empty environment. -/
def empty : Env := ⟨[], []⟩

/-- The first of four modifiers. -/
def firstOf : Expr → Expr
  | .app a _ => a
  | _ => .sym 0

/-- **The modifiers of a sort that may have bound variables**: four modifiers whose second is `strict_no`. -/
def isUnstrict (m : Expr) : Bool :=
  decide (m = modifiers (firstOf m) (node "strict_no" []) (thirdOf m) (fourthOf m))

theorem isUnstrict_iff {m : Expr} :
    isUnstrict m = true ↔ ∃ p pr f, m = modifiers p (node "strict_no" []) pr f := by
  constructor
  · intro unstrict
    exact ⟨_, _, _, of_decide_eq_true unstrict⟩
  · rintro ⟨p, pr, f, rfl⟩
    exact decide_eq_true rfl

/-- Every dependency is a bound variable declared before. -/
def depsBound (bound deps : List Expr) : Bool := deps.all fun d => decide (d ∈ bound)

/-- The names of a bound group: each is no binder name yet; each becomes a binder name and a bound variable. -/
def declareBound : List Expr → List Expr → List Expr → Option (List Expr × List Expr)
  | [], bound, names => some (bound, names)
  | x :: xs, bound, names => if x ∈ names then none else declareBound xs (x :: bound) (x :: names)

/-- The names of a regular group: each named binder is no binder name yet and becomes one. -/
def declareRegular : List (Option Expr) → List Expr → Option (List Expr)
  | [], names => some names
  | some x :: xs, names => if x ∈ names then none else declareRegular xs (x :: names)
  | none :: xs, names => declareRegular xs names

/-- **MM0's rules for the binder groups of a term**, in order, from the bound variables and binder names so far. -/
def checkGroups (sorts : SortEnv) : List Group → List Expr → List Expr → Option (List Expr × List Expr)
  | [], bound, names => some (bound, names)
  | .bound xs ty :: gs, bound, names =>
      if ty.deps = [] ∧ (lookupSort sorts ty.sort).map isUnstrict = some true then
        (declareBound xs bound names).bind fun state => checkGroups sorts gs state.1 state.2
      else none
  | .regular xs ty :: gs, bound, names =>
      if (lookupSort sorts ty.sort).isSome ∧ depsBound bound ty.deps = true then
        (declareRegular xs names).bind fun names' => checkGroups sorts gs bound names'
      else none

/-- **MM0's rules for the arrow type of a term**, with its bound variables. -/
def checkArrow (sorts : SortEnv) (bound : List Expr) : List Typ → Typ → Bool
  | [], r => decide ((lookupSort sorts r.sort).map isTarget = some true) && depsBound bound r.deps
  | a :: as, r => (lookupSort sorts a.sort).isSome && depsBound bound a.deps && checkArrow sorts bound as r

/-- **The verdict of a term's signature**: its groups, then its arrow type. -/
def verdict (sorts : SortEnv) (t : TermStatement) : Bool :=
  match checkGroups sorts t.groups [] [] with
  | none => false
  | some state => checkArrow sorts state.1 t.args t.ret

/-- **MM0's rules for a term declaration**: its name is no term's, and its signature passes. -/
def checkTerm (env : Env) (t : TermStatement) : Option Env :=
  if t.name ∉ env.terms ∧ verdict env.sorts t = true then some ⟨env.sorts, t.name :: env.terms⟩ else none

/-- MM0's rule for one statement. -/
def checkStatement (env : Env) : Statement → Option Env
  | .sort d => (declare env.sorts d).map fun sorts => ⟨sorts, env.terms⟩
  | .term t => checkTerm env t

/-- **MM0's rules for a file of statements**, in order. -/
def checkAll : Env → List Statement → Option Env
  | env, [] => some env
  | env, s :: ss => (checkStatement env s).bind fun env' => checkAll env' ss

/-! ## What is left to check of a term -/

/-- The verdict after the groups `gs`, from the bound variables and names so far. -/
def afterGroups (sorts : SortEnv) (t : TermStatement) (gs : List Group) (bound names : List Expr) : Bool :=
  match checkGroups sorts gs bound names with
  | none => false
  | some state => checkArrow sorts state.1 t.args t.ret

/-- The verdict after the names `xs` of a bound group, then the groups `gs`. -/
def afterBound (sorts : SortEnv) (t : TermStatement) (xs : List Expr) (gs : List Group)
    (bound names : List Expr) : Bool :=
  match declareBound xs bound names with
  | none => false
  | some state => afterGroups sorts t gs state.1 state.2

/-- The verdict after the names `xs` of a regular group, then the groups `gs`. -/
def afterRegular (sorts : SortEnv) (t : TermStatement) (xs : List (Option Expr)) (gs : List Group)
    (bound names : List Expr) : Bool :=
  match declareRegular xs names with
  | none => false
  | some names' => afterGroups sorts t gs bound names'

theorem verdict_eq (sorts : SortEnv) (t : TermStatement) : verdict sorts t = afterGroups sorts t t.groups [] [] :=
  rfl

/-! ## The store -/

/-- The binder rows of a term under check: a binder name row per name, a bound variable row per bound variable. -/
def current (t : Expr) (bound names : List Expr) : List Expr := names.map (binderName t) ++ bound.map (boundVar t)

/-- **The rows of the store besides the cursor**: the sort rows, the term name rows, the binder rows. -/
def storeBag (env : Env) (locals : List Expr) : Multiset Expr :=
  (envRows env.sorts : Multiset Expr) + (env.terms.map termName : Multiset Expr) + (locals : Multiset Expr)

/-- Binder rows keyed by names among `keys`. -/
def LocalsIn (keys locals : List Expr) : Prop :=
  ∀ e ∈ locals, ∃ u ∈ keys, ∃ x, e = binderName u x ∨ e = boundVar u x

/-- **The bag of a file**: its cursor row alone. -/
def start (ss : List Statement) : Multiset Expr :=
  (([pending (fileTree (ss.map Statement.tree))] : List Expr) : Multiset Expr)

theorem mem_storeBag {e : Expr} {env : Env} {locals : List Expr} :
    e ∈ storeBag env locals ↔ e ∈ envRows env.sorts ∨ e ∈ env.terms.map termName ∨ e ∈ locals := by
  simp only [storeBag, Multiset.mem_add, Multiset.mem_coe, or_assoc]

theorem kind_of_mem_storeBag {e : Expr} {env : Env} {keys locals : List Expr} (shape : LocalsIn keys locals)
    (inside : e ∈ storeBag env locals) :
    kindOf e = some 1 ∨ kindOf e = some 2 ∨ kindOf e = some 3 ∨ kindOf e = some 12 ∨ kindOf e = some 13 := by
  rcases mem_storeBag.mp inside with sorted | named | local'
  · rcases SortDeclarations.kind_of_mem_envRows sorted with one | two
    · exact Or.inl one
    · exact Or.inr (Or.inl two)
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp named
    exact Or.inr (Or.inr (Or.inl rfl))
  · obtain ⟨u, -, x, rfl | rfl⟩ := shape e local'
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- **A rule takes the row beside a store whose rows are of other kinds.** -/
theorem take_inv {θ : ℕ → Expr} {k : ℕ} {args : List Tm} {rest : Multiset Expr} {c : Expr}
    {rows : Multiset Expr}
    (split : (([inst θ (rowP k args)] : List Expr) : Multiset Expr) + rest =
      (([c] : List Expr) : Multiset Expr) + rows)
    (kinds : ∀ e ∈ rows, kindOf e ≠ some k) :
    row k (args.map (inst θ)) = c ∧ rest = rows := by
  have inside : inst θ (rowP k args) ∈ (([c] : List Expr) : Multiset Expr) + rows := by
    rw [← split]
    exact mem_one_add.mpr (Or.inl rfl)
  rw [inst_rowP] at inside
  rcases mem_one_add.mp inside with same | there
  · refine ⟨same, ?_⟩
    rw [inst_rowP, same] at split
    exact add_left_cancel split
  · exact absurd (kindOf_row k _) (kinds _ there)

/-- The kinds of a store are not the kinds the rules take. -/
theorem store_kinds {env : Env} {keys locals : List Expr} (shape : LocalsIn keys locals) {k : ℕ}
    (notStore : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 12 ∧ k ≠ 13) : ∀ e ∈ storeBag env locals, kindOf e ≠ some k := by
  intro e inside same
  rcases kind_of_mem_storeBag shape inside with h | h | h | h | h <;>
    (rw [same] at h; simp only [Option.some.injEq] at h; omega)

theorem localsIn_append {keys old new : List Expr} (first : LocalsIn keys old) (second : LocalsIn keys new) :
    LocalsIn keys (old ++ new) := by
  intro e inside
  rcases List.mem_append.mp inside with early | late
  · exact first e early
  · exact second e late

theorem localsIn_current (t : Expr) (bound names : List Expr) {keys : List Expr} (member : t ∈ keys) :
    LocalsIn keys (current t bound names) := by
  intro e inside
  rcases List.mem_append.mp inside with named | bounded
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp named
    exact ⟨t, member, x, Or.inl rfl⟩
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp bounded
    exact ⟨t, member, x, Or.inr rfl⟩

theorem localsIn_mono {keys keys' locals : List Expr} (shape : LocalsIn keys locals)
    (sub : ∀ u ∈ keys, u ∈ keys') : LocalsIn keys' locals := by
  intro e inside
  obtain ⟨u, member, x, same⟩ := shape e inside
  exact ⟨u, sub u member, x, same⟩

theorem localsIn_term {terms old : List Expr} (shape : LocalsIn terms old) (t : Expr) (bound names : List Expr) :
    LocalsIn (t :: terms) (old ++ current t bound names) :=
  localsIn_append (localsIn_mono shape fun _ member => List.mem_cons_of_mem _ member)
    (localsIn_current _ _ _ List.mem_cons_self)

/-- A binder name row of the term under check is in the store exactly when the name is a binder name of it. -/
theorem binderName_mem {env : Env} {t x : Expr} {old bound names : List Expr} (shape : LocalsIn env.terms old)
    (fresh : t ∉ env.terms) :
    binderName t x ∈ storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t bound names) ↔ x ∈ names := by
  constructor
  · intro inside
    rcases mem_storeBag.mp inside with sorted | named | local'
    · rcases SortDeclarations.kind_of_mem_envRows sorted with h | h <;> simp [binderName] at h
    · obtain ⟨u, -, same⟩ := List.mem_map.mp named
      exact absurd (row_inj.mp same).1 (by decide)
    · rcases List.mem_append.mp local' with early | late
      · obtain ⟨u, member, y, same | same⟩ := shape _ early
        · have keys : t = u := (List.cons.inj (row_inj.mp same).2).1
          subst keys
          exact absurd member fresh
        · exact absurd (row_inj.mp same).1 (by decide)
      · rcases List.mem_append.mp late with named' | bounded
        · obtain ⟨y, member, same⟩ := List.mem_map.mp named'
          have args := (row_inj.mp same).2
          rw [← (List.cons.inj (List.cons.inj args).2).1]
          exact member
        · obtain ⟨y, -, same⟩ := List.mem_map.mp bounded
          exact absurd (row_inj.mp same).1 (by decide)
  · intro member
    exact mem_storeBag.mpr (Or.inr (Or.inr (List.mem_append_right _
      (List.mem_append_left _ (List.mem_map_of_mem member)))))

/-- A bound variable row of the term under check is in the store exactly when it is a bound variable of it. -/
theorem boundVar_mem {env : Env} {t x : Expr} {old bound names : List Expr} (shape : LocalsIn env.terms old)
    (fresh : t ∉ env.terms) :
    boundVar t x ∈ storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t bound names) ↔ x ∈ bound := by
  constructor
  · intro inside
    rcases mem_storeBag.mp inside with sorted | named | local'
    · rcases SortDeclarations.kind_of_mem_envRows sorted with h | h <;> simp [boundVar] at h
    · obtain ⟨u, -, same⟩ := List.mem_map.mp named
      exact absurd (row_inj.mp same).1 (by decide)
    · rcases List.mem_append.mp local' with early | late
      · obtain ⟨u, member, y, same | same⟩ := shape _ early
        · exact absurd (row_inj.mp same).1 (by decide)
        · have keys : t = u := (List.cons.inj (row_inj.mp same).2).1
          subst keys
          exact absurd member fresh
      · rcases List.mem_append.mp late with named' | bounded
        · obtain ⟨y, -, same⟩ := List.mem_map.mp named'
          exact absurd (row_inj.mp same).1 (by decide)
        · obtain ⟨y, member, same⟩ := List.mem_map.mp bounded
          have args := (row_inj.mp same).2
          rw [← (List.cons.inj (List.cons.inj args).2).1]
          exact member
  · intro member
    exact mem_storeBag.mpr (Or.inr (Or.inr (List.mem_append_right _
      (List.mem_append_right _ (List.mem_map_of_mem member)))))

theorem sortEntry_mem {env : Env} {keys locals : List Expr} (shape : LocalsIn keys locals) {s m : Expr} :
    sortEntry s m ∈ storeBag env locals ↔ (s, m) ∈ env.sorts := by
  constructor
  · intro inside
    rcases mem_storeBag.mp inside with sorted | named | local'
    · exact sortEntry_mem_envRows.mp sorted
    · obtain ⟨u, -, same⟩ := List.mem_map.mp named
      exact absurd (row_inj.mp same).1 (by decide)
    · obtain ⟨u, -, x, same | same⟩ := shape _ local'
      · exact absurd (row_inj.mp same).1 (by decide)
      · exact absurd (row_inj.mp same).1 (by decide)
  · exact fun member => mem_storeBag.mpr (Or.inl (sortEntry_mem_envRows.mpr member))

theorem sortName_mem {env : Env} {keys locals : List Expr} (shape : LocalsIn keys locals) {s : Expr} :
    sortName s ∈ storeBag env locals ↔ s ∈ env.sorts.map Prod.fst := by
  constructor
  · intro inside
    rcases mem_storeBag.mp inside with sorted | named | local'
    · exact sortName_mem_envRows.mp sorted
    · obtain ⟨u, -, same⟩ := List.mem_map.mp named
      exact absurd (row_inj.mp same).1 (by decide)
    · obtain ⟨u, -, x, same | same⟩ := shape _ local'
      · exact absurd (row_inj.mp same).1 (by decide)
      · exact absurd (row_inj.mp same).1 (by decide)
  · exact fun member => mem_storeBag.mpr (Or.inl (sortName_mem_envRows.mpr member))

theorem termName_mem {env : Env} {keys locals : List Expr} (shape : LocalsIn keys locals) {t : Expr} :
    termName t ∈ storeBag env locals ↔ t ∈ env.terms := by
  constructor
  · intro inside
    rcases mem_storeBag.mp inside with sorted | named | local'
    · rcases SortDeclarations.kind_of_mem_envRows sorted with h | h <;> simp [termName] at h
    · obtain ⟨u, member, same⟩ := List.mem_map.mp named
      rw [← (List.cons.inj (row_inj.mp same).2).1]
      exact member
    · obtain ⟨u, -, x, same | same⟩ := shape _ local'
      · exact absurd (row_inj.mp same).1 (by decide)
      · exact absurd (row_inj.mp same).1 (by decide)
  · exact fun member => mem_storeBag.mpr (Or.inr (Or.inl (List.mem_map_of_mem member)))

/-! ## Rearranging the store -/

theorem coe_cons' {a : Expr} {l : List Expr} :
    ((a :: l : List Expr) : Multiset Expr) = {a} + (l : Multiset Expr) := by
  rw [← Multiset.cons_coe, ← Multiset.singleton_add]

theorem coe_append' {l l' : List Expr} :
    ((l ++ l' : List Expr) : Multiset Expr) = (l : Multiset Expr) + (l' : Multiset Expr) :=
  (Multiset.coe_add l l').symm

theorem declared_store (s m r : Expr) (env : Env) (old : List Expr) :
    (([sortName s, sortEntry s m, pending r] : List Expr) : Multiset Expr) + storeBag env old =
      (([pending r] : List Expr) : Multiset Expr) + storeBag ⟨(s, m) :: env.sorts, env.terms⟩ old := by
  simp only [storeBag, envRows, coe_cons', Multiset.coe_nil, add_zero]
  abel

theorem named_store (t c : Expr) (env : Env) (old : List Expr) :
    (([termName t, c] : List Expr) : Multiset Expr) + storeBag env old =
      (([c] : List Expr) : Multiset Expr) + storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t [] []) := by
  simp only [storeBag, current, List.map_cons, List.map_nil, List.append_nil, coe_cons', Multiset.coe_nil,
    add_zero]
  abel

theorem bound_store (t x c : Expr) (env : Env) (old bound names : List Expr) :
    (([binderName t x, boundVar t x, c] : List Expr) : Multiset Expr) +
        storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t bound names) =
      (([c] : List Expr) : Multiset Expr) +
        storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t (x :: bound) (x :: names)) := by
  simp only [storeBag, current, List.map_cons, coe_append', coe_cons', Multiset.coe_nil, add_zero]
  abel

theorem regular_store (t x c : Expr) (env : Env) (old bound names : List Expr) :
    (([binderName t x, c] : List Expr) : Multiset Expr) +
        storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t bound names) =
      (([c] : List Expr) : Multiset Expr) +
        storeBag ⟨env.sorts, t :: env.terms⟩ (old ++ current t bound (x :: names)) := by
  simp only [storeBag, current, List.map_cons, coe_append', coe_cons', Multiset.coe_nil, add_zero]
  abel

/-! ## Inversions -/

theorem statement_cases {x : Expr} {s : Statement} {ss : List Statement} {g : Expr}
    (same : node "file_more" [x, g] = fileTree ((s :: ss).map Statement.tree)) :
    x = s.tree ∧ g = fileTree (ss.map Statement.tree) := by
  obtain ⟨first, rest⟩ := List.cons.inj (node_inj.mp same).2
  exact ⟨first, (List.cons.inj rest).1⟩

/-- The three parts of a node with three children. -/
theorem node3_inv {l l' : String} {a b c a' b' c' : Expr} (same : node l [a, b, c] = node l' [a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  have parts := (node_inj.mp same).2
  obtain ⟨ha, parts⟩ := List.cons.inj parts
  obtain ⟨hb, parts⟩ := List.cons.inj parts
  exact ⟨ha, hb, (List.cons.inj parts).1⟩

/-- The two parts of a node with two children. -/
theorem node2_inv {l l' : String} {a b a' b' : Expr} (same : node l [a, b] = node l' [a', b']) :
    a = a' ∧ b = b' := by
  have parts := (node_inj.mp same).2
  obtain ⟨ha, parts⟩ := List.cons.inj parts
  exact ⟨ha, (List.cons.inj parts).1⟩

theorem typ_inv {a b : Expr} {ty : Typ} (same : node "typ_deps" [a, b] = ty.tree) :
    a = ty.sort ∧ b = idsTree ty.deps :=
  node2_inv same

/-! ## The invariant of every run -/

/-- **Where the check of a term can be**, and what is left to check from there: the verdict of the whole term's
signature is the verdict of what is left. -/
def InTerm (sorts : SortEnv) (t : TermStatement) (restTree : Expr) (bound names : List Expr) (cursor : Expr) :
    Prop :=
  (∃ gs, verdict sorts t = afterGroups sorts t gs bound names ∧
      cursor = binders t.name (groupsTree gs) (arrowTree t.args t.ret) restTree) ∨
    (∃ xs s gs, verdict sorts t = afterBound sorts t xs gs bound names ∧
      cursor = boundNames t.name (idsTree xs) s (groupsTree gs) (arrowTree t.args t.ret) restTree) ∨
    (∃ ds xs gs, verdict sorts t = (depsBound bound ds && afterRegular sorts t xs gs bound names) ∧
      cursor = regularDeps t.name (idsTree ds) (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree) ∨
    (∃ xs gs, verdict sorts t = afterRegular sorts t xs gs bound names ∧
      cursor = regularNames t.name (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree) ∨
    (∃ post, verdict sorts t = checkArrow sorts bound post t.ret ∧
      cursor = arrow t.name (arrowTree post t.ret) restTree) ∨
    (∃ ds post, verdict sorts t = (depsBound bound ds && checkArrow sorts bound post t.ret) ∧
      cursor = arrowDeps t.name (idsTree ds) (arrowTree post t.ret) restTree) ∨
    (∃ ds, verdict sorts t = depsBound bound ds ∧ cursor = returnDeps t.name (idsTree ds) restTree)

/-- **Where a run from a file can be.** -/
def Phase (ss₀ : List Statement) (bag : Multiset Expr) : Prop :=
  (∃ done rest env old, ss₀ = done ++ rest ∧ checkAll empty done = some env ∧ LocalsIn env.terms old ∧
      bag = (([pending (fileTree (rest.map Statement.tree))] : List Expr) : Multiset Expr) + storeBag env old) ∨
    (∃ done t rest env old bound names cursor, ss₀ = done ++ .term t :: rest ∧ checkAll empty done = some env ∧
      LocalsIn env.terms old ∧ t.name ∉ env.terms ∧
      InTerm env.sorts t (fileTree (rest.map Statement.tree)) bound names cursor ∧
      bag = (([cursor] : List Expr) : Multiset Expr) +
        storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names)) ∨
    (∃ env old, checkAll empty ss₀ = some env ∧ LocalsIn env.terms old ∧
      bag = (([accepted] : List Expr) : Multiset Expr) + storeBag env old)

theorem checkAll_append : ∀ (env : Env) (ss : List Statement) (s : Statement),
    checkAll env (ss ++ [s]) = (checkAll env ss).bind fun env' => checkStatement env' s
  | env, [], s => by
      show (checkStatement env s).bind (fun env' => some env') = checkStatement env s
      cases checkStatement env s <;> rfl
  | env, s' :: ss, s => by
      show (checkStatement env s').bind (fun e => checkAll e (ss ++ [s])) =
        ((checkStatement env s').bind fun e => checkAll e ss).bind fun e => checkStatement e s
      cases checkStatement env s' with
      | none => rfl
      | some env' => exact checkAll_append env' ss s

theorem checkStatement_nodup {env env' : Env} {s : Statement} (nodup : (env.sorts.map Prod.fst).Nodup)
    (checked : checkStatement env s = some env') : (env'.sorts.map Prod.fst).Nodup := by
  cases s with
  | sort d =>
      cases declared : declare env.sorts d with
      | none =>
          rw [show checkStatement env (.sort d) = (declare env.sorts d).map (fun sorts => ⟨sorts, env.terms⟩)
            from rfl, declared] at checked
          cases checked
      | some sorts =>
          rw [show checkStatement env (.sort d) = (declare env.sorts d).map (fun sorts => ⟨sorts, env.terms⟩)
            from rfl, declared] at checked
          cases checked
          exact declare_nodup nodup declared
  | term t =>
      rw [show checkStatement env (.term t) = checkTerm env t from rfl] at checked
      unfold checkTerm at checked
      split at checked
      · cases checked
        exact nodup
      · cases checked

theorem checkAll_nodup : ∀ {env env' : Env} {ss : List Statement}, (env.sorts.map Prod.fst).Nodup →
    checkAll env ss = some env' → (env'.sorts.map Prod.fst).Nodup
  | _, _, [], nodup, done => by
      cases done
      exact nodup
  | env, env', s :: ss, nodup, done => by
      rw [show checkAll env (s :: ss) = (checkStatement env s).bind (fun e => checkAll e ss) from rfl] at done
      cases checked : checkStatement env s with
      | none =>
          rw [checked] at done
          cases done
      | some env'' =>
          rw [checked] at done
          exact checkAll_nodup (checkStatement_nodup nodup checked) done

theorem storeBag_empty : storeBag empty [] = 0 := by simp [storeBag, empty, envRows]

theorem phase_start (ss₀ : List Statement) : Phase ss₀ (start ss₀) :=
  Or.inl ⟨[], ss₀, empty, [], rfl, rfl, fun e inside => absurd inside List.not_mem_nil,
    by rw [storeBag_empty, add_zero]; rfl⟩

/-- **Every rewrite keeps the invariant.** -/
theorem phase_step {ss₀ : List Statement} {bag bag' : Multiset Expr} (phase : Phase ss₀ bag)
    (step : RewritesNone program bag bag') : Phase ss₀ bag' := by
  obtain ⟨r, member, θ, rest, split, readsIn, -, nones, rfl⟩ := step
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases phase with ⟨done, rest₀, env, old, decomposed, checked, shape, rfl⟩ |
    ⟨done, t, rest₀, env, old, bound, names, cursor, decomposed, checked, shape, fresh, inTerm, rfl⟩ |
    ⟨env, old, checked, shape, rfl⟩
  · -- the cursor at the rest of the file
    have nodup := checkAll_nodup (env := empty) List.nodup_nil checked
    rcases member with rfl | rfl | rfl | rfl | member
    · -- declareSort
      obtain ⟨same, rfl⟩ := take_inv split (store_kinds shape (by decide))
      have file : node "file_more" [node "statement_sort" [θ 0, θ 1, θ 2, θ 3, θ 4], θ 5] =
          fileTree (rest₀.map Statement.tree) := (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil => exact absurd (node_inj.mp file).1 (by decide)
      | cons s ss =>
          obtain ⟨statement, hr⟩ := statement_cases file
          cases s with
          | term t => exact absurd (node_inj.mp statement).1 (by decide)
          | sort d =>
              have fields := (node_inj.mp statement).2
              obtain ⟨hp, fields⟩ := List.cons.inj fields
              obtain ⟨hst, fields⟩ := List.cons.inj fields
              obtain ⟨hpr, fields⟩ := List.cons.inj fields
              obtain ⟨hf, fields⟩ := List.cons.inj fields
              obtain ⟨hs, -⟩ := List.cons.inj fields
              have freshSort : sortName (θ 4) ∉ (([pending (fileTree ((Statement.sort d :: ss).map
                  Statement.tree))] : List Expr) : Multiset Expr) + storeBag env old :=
                nones (rowP 1 [u 4]) (List.mem_singleton_self _)
              have looked : lookupSort env.sorts d.name = none := lookupSort_eq_none_iff.mpr fun known =>
                freshSort (mem_one_add.mpr (Or.inr (by rw [hs]; exact (sortName_mem shape).mpr known)))
              have declared : checkStatement env (.sort d) =
                  some ⟨(d.name, d.mods) :: env.sorts, env.terms⟩ := by
                simp [checkStatement, declare, looked]
              refine Or.inl ⟨done ++ [.sort d], ss, ⟨(d.name, d.mods) :: env.sorts, env.terms⟩, old,
                by rw [decomposed, List.append_assoc, List.singleton_append],
                by rw [checkAll_append, checked]; exact declared, shape, ?_⟩
              show (([sortName (θ 4), sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)), pending (θ 5)] :
                  List Expr) : Multiset Expr) + storeBag env old = _
              rw [hp, hst, hpr, hf, hs, hr]
              exact declared_store _ _ _ env old
    · -- repeatSort
      obtain ⟨same, rfl⟩ := take_inv split (store_kinds shape (by decide))
      have file : node "file_more" [node "statement_sort" [θ 0, θ 1, θ 2, θ 3, θ 4], θ 5] =
          fileTree (rest₀.map Statement.tree) := (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil => exact absurd (node_inj.mp file).1 (by decide)
      | cons s ss =>
          obtain ⟨statement, hr⟩ := statement_cases file
          cases s with
          | term t => exact absurd (node_inj.mp statement).1 (by decide)
          | sort d =>
              have fields := (node_inj.mp statement).2
              obtain ⟨hp, fields⟩ := List.cons.inj fields
              obtain ⟨hst, fields⟩ := List.cons.inj fields
              obtain ⟨hpr, fields⟩ := List.cons.inj fields
              obtain ⟨hf, fields⟩ := List.cons.inj fields
              obtain ⟨hs, -⟩ := List.cons.inj fields
              have known : sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)) ∈ storeBag env old :=
                readsIn (rowP 2 [u 4, listP [u 0, u 1, u 2, u 3]]) (List.mem_singleton_self _)
              rw [hp, hst, hpr, hf, hs] at known
              have entered : (d.name, d.mods) ∈ env.sorts := (sortEntry_mem shape).mp known
              have declared : checkStatement env (.sort d) = some ⟨env.sorts, env.terms⟩ := by
                simp [checkStatement, declare, lookupSort_of_mem nodup entered]
              refine Or.inl ⟨done ++ [.sort d], ss, env, old,
                by rw [decomposed, List.append_assoc, List.singleton_append],
                by rw [checkAll_append, checked]; exact declared, shape, ?_⟩
              show (([pending (θ 5)] : List Expr) : Multiset Expr) + storeBag env old = _
              rw [hr]
    · -- acceptFile
      obtain ⟨same, rfl⟩ := take_inv split (store_kinds shape (by decide))
      have file : node "file_empty" [] = fileTree (rest₀.map Statement.tree) :=
        (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil =>
          exact Or.inr (Or.inr ⟨env, old, by rw [decomposed, List.append_nil]; exact checked, shape, rfl⟩)
      | cons s ss => exact absurd (node_inj.mp file).1 (by decide)
    · -- startTerm
      obtain ⟨same, rfl⟩ := take_inv split (store_kinds shape (by decide))
      have file : node "file_more" [node "statement_term" [θ 0, θ 1, θ 2], θ 3] =
          fileTree (rest₀.map Statement.tree) := (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil => exact absurd (node_inj.mp file).1 (by decide)
      | cons s ss =>
          obtain ⟨statement, hr⟩ := statement_cases file
          cases s with
          | sort d => exact absurd (node_inj.mp statement).1 (by decide)
          | term t =>
              obtain ⟨hn, hg, ha⟩ := node3_inv statement
              have freshTerm : termName (θ 0) ∉ (([pending (fileTree ((Statement.term t :: ss).map
                  Statement.tree))] : List Expr) : Multiset Expr) + storeBag env old :=
                nones (rowP 3 [u 0]) (List.mem_singleton_self _)
              have unnamed : t.name ∉ env.terms := fun known =>
                freshTerm (mem_one_add.mpr (Or.inr (by rw [hn]; exact (termName_mem shape).mpr known)))
              refine Or.inr (Or.inl ⟨done, t, ss, env, old, [], [], binders t.name (groupsTree t.groups)
                (arrowTree t.args t.ret) (fileTree (ss.map Statement.tree)), decomposed, checked, shape, unnamed,
                Or.inl ⟨t.groups, verdict_eq _ _, rfl⟩, ?_⟩)
              show (([termName (θ 0), binders (θ 0) (θ 1) (θ 2) (θ 3)] : List Expr) : Multiset Expr) +
                storeBag env old = _
              rw [hn, hg, ha, hr]
              exact named_store _ _ env old
    · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        exact (absurd (row_inj.mp (take_inv split (store_kinds shape (by decide))).1).1 (by decide))
  · -- a term under check
    have shape' : LocalsIn (t.name :: env.terms) (old ++ current t.name bound names) :=
      localsIn_term shape t.name bound names
    have nodup := checkAll_nodup (env := empty) List.nodup_nil checked
    have kinds := fun {k : ℕ} (notStore : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 12 ∧ k ≠ 13) =>
      store_kinds (env := ⟨env.sorts, t.name :: env.terms⟩) shape' notStore
    rcases inTerm with ⟨gs, vgs, rfl⟩ | ⟨xs, s, gs, vxs, rfl⟩ | ⟨ds, xs, gs, vds, rfl⟩ | ⟨xs, gs, vxs, rfl⟩ |
      ⟨post, vpost, rfl⟩ | ⟨ds, post, vds, rfl⟩ | ⟨ds, vds, rfl⟩
    · -- the groups `gs` left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- boundGroup
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "tbinders_more" [node "tbinder_bound" [θ 1, node "typ_deps" [θ 2,
            node "ids_empty" []]], θ 3], θ 4, θ 5] =
            [t.name, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases gs with
        | nil => exact absurd (node_inj.mp hgs).1 (by decide)
        | cons g gs =>
            obtain ⟨hg, hmore⟩ := node2_inv hgs
            cases g with
            | regular xs ty => exact absurd (node_inj.mp hg).1 (by decide)
            | bound xs ty =>
                obtain ⟨hxs, htyp⟩ := node2_inv hg
                obtain ⟨hsort, hdeps⟩ := typ_inv htyp
                have noDeps : ty.deps = [] := by
                  cases ty with
                  | mk sort deps =>
                      cases deps with
                      | nil => rfl
                      | cons d ds => exact absurd (node_inj.mp hdeps).1 (by decide)
                have known : sortEntry (θ 2) (modifiers (θ 6) (node "strict_no" []) (θ 7) (θ 8)) ∈
                    storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
                  readsIn (rowP 2 [u 2, listP [u 6, nodeP "strict_no" [], u 7, u 8]]) (List.mem_singleton_self _)
                rw [hsort] at known
                have looked := lookupSort_of_mem nodup
                  ((sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩) shape').mp known)
                have unstrict : (lookupSort env.sorts ty.sort).map isUnstrict = some true := by
                  rw [looked]
                  exact congrArg some (isUnstrict_iff.mpr ⟨_, _, _, rfl⟩)
                refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, boundNames t.name (idsTree xs)
                  ty.sort (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)),
                  decomposed, checked, shape, fresh, Or.inr (Or.inl ⟨xs, ty.sort, gs, ?_, rfl⟩), ?_⟩)
                · rw [vgs]
                  unfold afterGroups afterBound
                  simp only [checkGroups, if_pos (And.intro noDeps unstrict)]
                  cases declareBound xs bound names <;> rfl
                · show (([boundNames (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)] : List Expr) : Multiset Expr) + _ = _
                  rw [hn, hxs, hsort, hmore, hty, hr]
      · -- regularGroup
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "tbinders_more" [node "tbinder_regular" [θ 1, node "typ_deps" [θ 2, θ 3]], θ 4],
            θ 5, θ 6] = [t.name, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases gs with
        | nil => exact absurd (node_inj.mp hgs).1 (by decide)
        | cons g gs =>
            obtain ⟨hg, hmore⟩ := node2_inv hgs
            cases g with
            | bound xs ty => exact absurd (node_inj.mp hg).1 (by decide)
            | regular xs ty =>
                obtain ⟨hxs, htyp⟩ := node2_inv hg
                obtain ⟨hsort, hdeps⟩ := typ_inv htyp
                have known : sortEntry (θ 2) (θ 7) ∈
                    storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
                  readsIn (rowP 2 [u 2, u 7]) (List.mem_singleton_self _)
                rw [hsort] at known
                have looked := lookupSort_of_mem nodup
                  ((sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩) shape').mp known)
                have declaredSort : (lookupSort env.sorts ty.sort).isSome = true :=
                  Option.isSome_iff_exists.mpr ⟨_, looked⟩
                refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, regularDeps t.name
                  (idsTree ty.deps) (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret)
                  (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
                  Or.inr (Or.inr (Or.inl ⟨ty.deps, xs, gs, ?_, rfl⟩)), ?_⟩)
                · rw [vgs]
                  unfold afterGroups afterRegular
                  by_cases allBound : depsBound bound ty.deps = true
                  · rw [show checkGroups env.sorts (.regular xs ty :: gs) bound names =
                        (declareRegular xs names).bind (fun names' => checkGroups env.sorts gs bound names') from
                        if_pos (And.intro declaredSort allBound), allBound, Bool.true_and]
                    cases declareRegular xs names <;> rfl
                  · simp [checkGroups, allBound]
                · show (([regularDeps (θ 0) (θ 3) (θ 1) (θ 4) (θ 5) (θ 6)] : List Expr) : Multiset Expr) + _ = _
                  rw [hn, hdeps, hxs, hmore, hty, hr]
      · -- bindersDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "tbinders_empty" [], θ 1, θ 2] =
            [t.name, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases gs with
        | cons g gs => exact absurd (node_inj.mp hgs).1 (by decide)
        | nil =>
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, arrow t.name (arrowTree t.args t.ret)
              (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t.args, vgs.trans rfl, rfl⟩)))), ?_⟩)
            show (([arrow (θ 0) (θ 1) (θ 2)] : List Expr) : Multiset Expr) + _ = _
            rw [hn, hty, hr]
    · -- the names `xs` of a bound group left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- boundName
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_more" [θ 1, θ 2], θ 3, θ 4, θ 5, θ 6] =
            [t.name, idsTree xs, s, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases xs with
        | nil => exact absurd (node_inj.mp hxs).1 (by decide)
        | cons x xs =>
            obtain ⟨hx, hrest⟩ := node2_inv hxs
            have freshName : binderName (θ 0) (θ 1) ∉ (([boundNames t.name (idsTree (x :: xs)) s (groupsTree gs)
                (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree))] : List Expr) : Multiset Expr) +
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              nones (rowP 12 [u 0, u 1]) (List.mem_singleton_self _)
            have unnamed : x ∉ names := fun known =>
              freshName (mem_one_add.mpr (Or.inr (by rw [hn, hx]; exact (binderName_mem shape fresh).mpr known)))
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, x :: bound, x :: names, boundNames t.name (idsTree xs)
              s (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)), decomposed, checked,
              shape, fresh, Or.inr (Or.inl ⟨xs, s, gs, ?_, rfl⟩), ?_⟩)
            · rw [vxs]
              simp only [afterBound, declareBound, if_neg unnamed]
            · show (([binderName (θ 0) (θ 1), boundVar (θ 0) (θ 1), boundNames (θ 0) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6)] :
                  List Expr) : Multiset Expr) + _ = _
              rw [hn, hx, hrest, hs, hgs, hty, hr]
              exact bound_store _ _ _ env old bound names
      · -- boundNamesDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_empty" [], θ 1, θ 2, θ 3, θ 4] =
            [t.name, idsTree xs, s, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases xs with
        | cons x xs => exact absurd (node_inj.mp hxs).1 (by decide)
        | nil =>
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, binders t.name (groupsTree gs)
              (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inl ⟨gs, vxs.trans rfl, rfl⟩, ?_⟩)
            show (([binders (θ 0) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
            rw [hn, hgs, hty, hr]
    · -- the dependencies `ds` of a regular group left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- regularDep
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_more" [θ 1, θ 2], θ 3, θ 4, θ 5, θ 6] =
            [t.name, idsTree ds, bidsTree xs, groupsTree gs, arrowTree t.args t.ret,
              fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | nil => exact absurd (node_inj.mp hds).1 (by decide)
        | cons d ds =>
            obtain ⟨hd, hrest⟩ := node2_inv hds
            have known : boundVar (θ 0) (θ 1) ∈
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              readsIn (rowP 13 [u 0, u 1]) (List.mem_singleton_self _)
            rw [hn, hd] at known
            have isBound : d ∈ bound := (boundVar_mem shape fresh).mp known
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, regularDeps t.name (idsTree ds)
              (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)),
              decomposed, checked, shape, fresh, Or.inr (Or.inr (Or.inl ⟨ds, xs, gs, ?_, rfl⟩)), ?_⟩)
            · rw [vds]
              simp [depsBound, isBound]
            · show (([regularDeps (θ 0) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hrest, hxs, hgs, hty, hr]
      · -- regularDepsDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_empty" [], θ 1, θ 2, θ 3, θ 4] =
            [t.name, idsTree ds, bidsTree xs, groupsTree gs, arrowTree t.args t.ret,
              fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | cons d ds => exact absurd (node_inj.mp hds).1 (by decide)
        | nil =>
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, regularNames t.name
              (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)),
              decomposed, checked, shape, fresh, Or.inr (Or.inr (Or.inr (Or.inl ⟨xs, gs, ?_, rfl⟩))), ?_⟩)
            · rw [vds]
              simp [depsBound]
            · show (([regularNames (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hxs, hgs, hty, hr]
    · -- the names `xs` of a regular group left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- regularName
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "bids_more" [θ 1, θ 2], θ 3, θ 4, θ 5] =
            [t.name, bidsTree xs, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases xs with
        | nil => exact absurd (node_inj.mp hxs).1 (by decide)
        | cons x xs =>
            cases x with
            | none => exact absurd (node_inj.mp hxs).1 (by decide)
            | some x =>
                obtain ⟨hx, hrest⟩ := node2_inv hxs
                have freshName : binderName (θ 0) (θ 1) ∉ (([regularNames t.name (bidsTree (some x :: xs))
                    (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree))] : List Expr) :
                    Multiset Expr) + storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
                  nones (rowP 12 [u 0, u 1]) (List.mem_singleton_self _)
                have unnamed : x ∉ names := fun known =>
                  freshName (mem_one_add.mpr (Or.inr (by
                    rw [hn, hx]
                    exact (binderName_mem shape fresh).mpr known)))
                refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, x :: names, regularNames t.name
                  (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)),
                  decomposed, checked, shape, fresh, Or.inr (Or.inr (Or.inr (Or.inl ⟨xs, gs, ?_, rfl⟩))), ?_⟩)
                · rw [vxs]
                  simp only [afterRegular, declareRegular, if_neg unnamed]
                · show (([binderName (θ 0) (θ 1), regularNames (θ 0) (θ 2) (θ 3) (θ 4) (θ 5)] : List Expr) :
                      Multiset Expr) + _ = _
                  rw [hn, hx, hrest, hgs, hty, hr]
                  exact regular_store _ _ _ env old bound names
      · -- regularBlank
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "bids_blank" [θ 1], θ 2, θ 3, θ 4] =
            [t.name, bidsTree xs, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases xs with
        | nil => exact absurd (node_inj.mp hxs).1 (by decide)
        | cons x xs =>
            cases x with
            | some x => exact absurd (node_inj.mp hxs).1 (by decide)
            | none =>
                have hrest : θ 1 = bidsTree xs := (List.cons.inj (node_inj.mp hxs).2).1
                refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, regularNames t.name (bidsTree xs)
                  (groupsTree gs) (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)), decomposed,
                  checked, shape, fresh, Or.inr (Or.inr (Or.inr (Or.inl ⟨xs, gs, vxs.trans rfl, rfl⟩))), ?_⟩)
                show (([regularNames (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
                rw [hn, hrest, hgs, hty, hr]
      · -- regularNamesDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "bids_empty" [], θ 1, θ 2, θ 3] =
            [t.name, bidsTree xs, groupsTree gs, arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hxs, parts⟩ := List.cons.inj parts
        obtain ⟨hgs, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases xs with
        | cons x xs =>
            cases x with
            | some x => exact absurd (node_inj.mp hxs).1 (by decide)
            | none => exact absurd (node_inj.mp hxs).1 (by decide)
        | nil =>
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, binders t.name (groupsTree gs)
              (arrowTree t.args t.ret) (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inl ⟨gs, vxs.trans rfl, rfl⟩, ?_⟩)
            show (([binders (θ 0) (θ 1) (θ 2) (θ 3)] : List Expr) : Multiset Expr) + _ = _
            rw [hn, hgs, hty, hr]
    · -- the arrow types `post` left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- arrowArgument
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "arrow_more" [node "typ_deps" [θ 1, θ 2], θ 3], θ 4] =
            [t.name, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hpost, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases post with
        | nil => exact absurd (node_inj.mp hpost).1 (by decide)
        | cons a post =>
            obtain ⟨htyp, htail⟩ := node2_inv hpost
            obtain ⟨hsort, hdeps⟩ := typ_inv htyp
            have known : sortEntry (θ 1) (θ 5) ∈
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              readsIn (rowP 2 [u 1, u 5]) (List.mem_singleton_self _)
            rw [hsort] at known
            have looked := lookupSort_of_mem nodup
              ((sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩) shape').mp known)
            have declaredSort : (lookupSort env.sorts a.sort).isSome = true :=
              Option.isSome_iff_exists.mpr ⟨_, looked⟩
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, arrowDeps t.name (idsTree a.deps)
              (arrowTree post t.ret) (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a.deps, post, ?_, rfl⟩))))), ?_⟩)
            · rw [vpost]
              simp only [checkArrow, declaredSort, Bool.true_and]
            · show (([arrowDeps (θ 0) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hdeps, htail, hr]
      · -- arrowReturn
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "arrow_last" [node "typ_deps" [θ 1, θ 2]], θ 3] =
            [t.name, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hpost, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases post with
        | cons a post => exact absurd (node_inj.mp hpost).1 (by decide)
        | nil =>
            have htyp : node "typ_deps" [θ 1, θ 2] = t.ret.tree := (List.cons.inj (node_inj.mp hpost).2).1
            obtain ⟨hsort, hdeps⟩ := typ_inv htyp
            have known : sortEntry (θ 1) (modifiers (node "pure_no" []) (θ 4) (θ 5) (θ 6)) ∈
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              readsIn (rowP 2 [u 1, listP [nodeP "pure_no" [], u 4, u 5, u 6]]) (List.mem_singleton_self _)
            rw [hsort] at known
            have looked := lookupSort_of_mem nodup
              ((sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩) shape').mp known)
            have target : decide ((lookupSort env.sorts t.ret.sort).map isTarget = some true) = true := by
              rw [looked]
              exact decide_eq_true (congrArg some (isTarget_iff.mpr ⟨_, _, _, rfl⟩))
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, returnDeps t.name (idsTree t.ret.deps)
              (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t.ret.deps, ?_, rfl⟩))))), ?_⟩)
            · rw [vpost]
              simp only [checkArrow, target, Bool.true_and]
            · show (([returnDeps (θ 0) (θ 2) (θ 3)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hdeps, hr]
    · -- the dependencies `ds` of an argument type left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- arrowDep
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_more" [θ 1, θ 2], θ 3, θ 4] =
            [t.name, idsTree ds, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨htail, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | nil => exact absurd (node_inj.mp hds).1 (by decide)
        | cons d ds =>
            obtain ⟨hd, hrest⟩ := node2_inv hds
            have known : boundVar (θ 0) (θ 1) ∈
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              readsIn (rowP 13 [u 0, u 1]) (List.mem_singleton_self _)
            rw [hn, hd] at known
            have isBound : d ∈ bound := (boundVar_mem shape fresh).mp known
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, arrowDeps t.name (idsTree ds)
              (arrowTree post t.ret) (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ds, post, ?_, rfl⟩))))), ?_⟩)
            · rw [vds]
              simp [depsBound, isBound]
            · show (([arrowDeps (θ 0) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hrest, htail, hr]
      · -- arrowDepsDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_empty" [], θ 1, θ 2] =
            [t.name, idsTree ds, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨htail, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | cons d ds => exact absurd (node_inj.mp hds).1 (by decide)
        | nil =>
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, arrow t.name (arrowTree post t.ret)
              (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨post, by rw [vds]; simp [depsBound], rfl⟩)))), ?_⟩)
            show (([arrow (θ 0) (θ 1) (θ 2)] : List Expr) : Multiset Expr) + _ = _
            rw [hn, htail, hr]
    · -- the dependencies `ds` of the return type left
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (absurd (row_inj.mp (take_inv split (kinds (by decide))).1).1 (by decide))
        | skip
      · -- returnDep
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_more" [θ 1, θ 2], θ 3] =
            [t.name, idsTree ds, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | nil => exact absurd (node_inj.mp hds).1 (by decide)
        | cons d ds =>
            obtain ⟨hd, hrest⟩ := node2_inv hds
            have known : boundVar (θ 0) (θ 1) ∈
                storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) :=
              readsIn (rowP 13 [u 0, u 1]) (List.mem_singleton_self _)
            rw [hn, hd] at known
            have isBound : d ∈ bound := (boundVar_mem shape fresh).mp known
            refine Or.inr (Or.inl ⟨done, t, rest₀, env, old, bound, names, returnDeps t.name (idsTree ds)
              (fileTree (rest₀.map Statement.tree)), decomposed, checked, shape, fresh,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ds, ?_, rfl⟩))))), ?_⟩)
            · rw [vds]
              simp [depsBound, isBound]
            · show (([returnDeps (θ 0) (θ 2) (θ 3)] : List Expr) : Multiset Expr) + _ = _
              rw [hn, hrest, hr]
      · -- returnDepsDone
        obtain ⟨same, rfl⟩ := take_inv split (kinds (by decide))
        have parts : [θ 0, node "ids_empty" [], θ 1] =
            [t.name, idsTree ds, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨hds, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        cases ds with
        | cons d ds => exact absurd (node_inj.mp hds).1 (by decide)
        | nil =>
            have passes : verdict env.sorts t = true := vds.trans rfl
            have declared : checkStatement env (.term t) = some ⟨env.sorts, t.name :: env.terms⟩ := by
              show checkTerm env t = _
              unfold checkTerm
              rw [if_pos ⟨fresh, passes⟩]
            refine Or.inl ⟨done ++ [.term t], rest₀, ⟨env.sorts, t.name :: env.terms⟩,
              old ++ current t.name bound names, by rw [decomposed, List.append_assoc, List.singleton_append],
              by rw [checkAll_append, checked]; exact declared, shape', ?_⟩
            show (([pending (θ 1)] : List Expr) : Multiset Expr) + _ = _
            rw [hr]
  · -- accepted: no rule takes
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (absurd (row_inj.mp (take_inv split (store_kinds shape (by decide))).1).1 (by decide))

theorem phase_multi {ss₀ : List Statement} : ∀ {bag bag' : (rewritingNone program).Term},
    (rewritingNone program).MultiStep bag bag' → Phase ss₀ bag → Phase ss₀ bag'
  | _, _, .refl _, phase => phase
  | _, _, .step first rest, phase => phase_multi rest (phase_step phase first)

theorem accepted_of_phase {ss₀ : List Statement} {bag : Multiset Expr} (phase : Phase ss₀ bag)
    (inside : accepted ∈ bag) : (checkAll empty ss₀).isSome := by
  rcases phase with ⟨done, rest, env, old, -, -, shape, rfl⟩ |
    ⟨done, t, rest, env, old, bound, names, cursor, -, -, shape, -, inTerm, rfl⟩ | ⟨env, old, checked, -, -⟩
  · rcases mem_one_add.mp inside with same | there
    · exact absurd (row_inj.mp same).1 (by decide)
    · rcases kind_of_mem_storeBag shape there with h | h | h | h | h <;> simp [accepted] at h
  · rcases mem_one_add.mp inside with same | there
    · rcases inTerm with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ |
        ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact absurd (row_inj.mp same).1 (by decide)
    · rcases kind_of_mem_storeBag (localsIn_term shape t.name bound names) there with h | h | h | h | h <;>
        simp [accepted] at h
  · simp [checked]

/-! ## The runs -/

/-- **From a cursor of the term under check, a run reaches the rest of the file**, with some binder rows. -/
def Reaches (t : TermStatement) (restTree : Expr) (env : Env) (old : List Expr) (cursor : Expr)
    (bound names : List Expr) : Prop :=
  ∃ bound' names', (rewritingNone program).MultiStep
    ((([cursor] : List Expr) : Multiset Expr) +
      storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
    ((([pending restTree] : List Expr) : Multiset Expr) +
      storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound' names'))

theorem deps_runs_regular (t : TermStatement) (restTree : Expr) (env : Env) (old bound names : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) (xs : List (Option Expr)) (gs : List Group) :
    ∀ ds : List Expr, depsBound bound ds = true →
      (rewritingNone program).MultiStep
        ((([regularDeps t.name (idsTree ds) (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree] :
          List Expr) : Multiset Expr) + storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
        ((([regularNames t.name (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree] :
          List Expr) : Multiset Expr) + storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
  | [], _ => .step (regularDepsDone_fires _ _ _ _ _ _) (.refl _)
  | d :: ds, allBound => by
      simp only [depsBound, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at allBound
      exact .step (regularDep_fires _ _ _ _ _ _ _ _ ((boundVar_mem shape fresh).mpr allBound.1))
        (deps_runs_regular t restTree env old bound names shape fresh xs gs ds allBound.2)

theorem deps_runs_arrow (t : TermStatement) (restTree : Expr) (env : Env) (old bound names : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) (post : List Typ) :
    ∀ ds : List Expr, depsBound bound ds = true →
      (rewritingNone program).MultiStep
        ((([arrowDeps t.name (idsTree ds) (arrowTree post t.ret) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
        ((([arrow t.name (arrowTree post t.ret) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
  | [], _ => .step (arrowDepsDone_fires _ _ _ _) (.refl _)
  | d :: ds, allBound => by
      simp only [depsBound, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at allBound
      exact .step (arrowDep_fires _ _ _ _ _ _ ((boundVar_mem shape fresh).mpr allBound.1))
        (deps_runs_arrow t restTree env old bound names shape fresh post ds allBound.2)

theorem deps_runs_return (t : TermStatement) (restTree : Expr) (env : Env) (old bound names : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) :
    ∀ ds : List Expr, depsBound bound ds = true →
      (rewritingNone program).MultiStep
        ((([returnDeps t.name (idsTree ds) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
        ((([pending restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
  | [], _ => .step (returnDepsDone_fires _ _ _) (.refl _)
  | d :: ds, allBound => by
      simp only [depsBound, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at allBound
      exact .step (returnDep_fires _ _ _ _ _ ((boundVar_mem shape fresh).mpr allBound.1))
        (deps_runs_return t restTree env old bound names shape fresh ds allBound.2)

theorem arrow_runs (t : TermStatement) (restTree : Expr) (env : Env) (old bound names : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) :
    ∀ post : List Typ, checkArrow env.sorts bound post t.ret = true →
      (rewritingNone program).MultiStep
        ((([arrow t.name (arrowTree post t.ret) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
        ((([pending restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names))
  | [], passes => by
      simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at passes
      obtain ⟨target, allBound⟩ := passes
      obtain ⟨m, looked⟩ : ∃ m, lookupSort env.sorts t.ret.sort = some m := by
        cases found : lookupSort env.sorts t.ret.sort with
        | none => rw [found] at target; cases target
        | some m => exact ⟨m, rfl⟩
      rw [looked] at target
      obtain ⟨st, pr, f, rfl⟩ := isTarget_iff.mp (Option.some.inj target)
      have known := (sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩)
        (localsIn_term shape t.name bound names)).mpr (mem_of_lookupSort looked)
      exact .step (arrowReturn_fires t.name t.ret.sort (idsTree t.ret.deps) restTree st pr f _ known)
        (deps_runs_return t restTree env old bound names shape fresh t.ret.deps allBound)
  | a :: post, passes => by
      simp only [checkArrow, Bool.and_eq_true] at passes
      obtain ⟨⟨declaredSort, allBound⟩, rest⟩ := passes
      obtain ⟨m, looked⟩ := Option.isSome_iff_exists.mp declaredSort
      have known := (sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩)
        (localsIn_term shape t.name bound names)).mpr (mem_of_lookupSort looked)
      exact .step (arrowArgument_fires t.name a.sort (idsTree a.deps) (arrowTree post t.ret) restTree m _ known)
        (multiStep_append (deps_runs_arrow t restTree env old bound names shape fresh post a.deps allBound)
          (arrow_runs t restTree env old bound names shape fresh post rest))

theorem bound_names_runs (t : TermStatement) (restTree : Expr) (env : Env) (old : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) (s : Expr) (gs : List Group)
    (cont : ∀ bound names, afterGroups env.sorts t gs bound names = true →
      Reaches t restTree env old (binders t.name (groupsTree gs) (arrowTree t.args t.ret) restTree) bound names) :
    ∀ (xs bound names : List Expr), afterBound env.sorts t xs gs bound names = true →
      Reaches t restTree env old
        (boundNames t.name (idsTree xs) s (groupsTree gs) (arrowTree t.args t.ret) restTree) bound names
  | [], bound, names, passes => by
      obtain ⟨bound', names', runs⟩ := cont bound names passes
      exact ⟨bound', names', .step (boundNamesDone_fires _ _ _ _ _ _) runs⟩
  | x :: xs, bound, names, passes => by
      have unnamed : x ∉ names := by
        intro known
        simp [afterBound, declareBound, known] at passes
      have passes' : afterBound env.sorts t xs gs (x :: bound) (x :: names) = true := by
        simpa [afterBound, declareBound, unnamed] using passes
      have freshName : binderName t.name x ∉ (([boundNames t.name (idsTree (x :: xs)) s (groupsTree gs)
          (arrowTree t.args t.ret) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) := by
        intro inside
        rcases mem_one_add.mp inside with same | there
        · exact absurd (row_inj.mp same).1 (by decide)
        · exact unnamed ((binderName_mem shape fresh).mp there)
      have first := boundName_fires t.name x (idsTree xs) s (groupsTree gs) (arrowTree t.args t.ret) restTree _
        freshName
      rw [bound_store] at first
      obtain ⟨bound', names', runs⟩ :=
        bound_names_runs t restTree env old shape fresh s gs cont xs (x :: bound) (x :: names) passes'
      exact ⟨bound', names', .step first runs⟩

theorem regular_names_runs (t : TermStatement) (restTree : Expr) (env : Env) (old : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) (gs : List Group)
    (cont : ∀ bound names, afterGroups env.sorts t gs bound names = true →
      Reaches t restTree env old (binders t.name (groupsTree gs) (arrowTree t.args t.ret) restTree) bound names) :
    ∀ (xs : List (Option Expr)) (bound names : List Expr), afterRegular env.sorts t xs gs bound names = true →
      Reaches t restTree env old
        (regularNames t.name (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree) bound names
  | [], bound, names, passes => by
      obtain ⟨bound', names', runs⟩ := cont bound names passes
      exact ⟨bound', names', .step (regularNamesDone_fires _ _ _ _ _) runs⟩
  | none :: xs, bound, names, passes => by
      obtain ⟨bound', names', runs⟩ := regular_names_runs t restTree env old shape fresh gs cont xs bound names passes
      exact ⟨bound', names', .step (regularBlank_fires _ _ _ _ _ _) runs⟩
  | some x :: xs, bound, names, passes => by
      have unnamed : x ∉ names := by
        intro known
        simp [afterRegular, declareRegular, known] at passes
      have passes' : afterRegular env.sorts t xs gs bound (x :: names) = true := by
        simpa [afterRegular, declareRegular, unnamed] using passes
      have freshName : binderName t.name x ∉ (([regularNames t.name (bidsTree (some x :: xs)) (groupsTree gs)
          (arrowTree t.args t.ret) restTree] : List Expr) : Multiset Expr) +
          storeBag ⟨env.sorts, t.name :: env.terms⟩ (old ++ current t.name bound names) := by
        intro inside
        rcases mem_one_add.mp inside with same | there
        · exact absurd (row_inj.mp same).1 (by decide)
        · exact unnamed ((binderName_mem shape fresh).mp there)
      have first := regularName_fires t.name x (bidsTree xs) (groupsTree gs) (arrowTree t.args t.ret) restTree _
        freshName
      rw [regular_store] at first
      obtain ⟨bound', names', runs⟩ :=
        regular_names_runs t restTree env old shape fresh gs cont xs bound (x :: names) passes'
      exact ⟨bound', names', .step first runs⟩

/-- **The groups run to the rest of the file** when what is left of the signature passes. -/
theorem groups_runs (t : TermStatement) (restTree : Expr) (env : Env) (old : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) :
    ∀ (gs : List Group) (bound names : List Expr), afterGroups env.sorts t gs bound names = true →
      Reaches t restTree env old (binders t.name (groupsTree gs) (arrowTree t.args t.ret) restTree) bound names
  | [], bound, names, passes =>
      ⟨bound, names, .step (bindersDone_fires _ _ _ _)
        (arrow_runs t restTree env old bound names shape fresh t.args passes)⟩
  | .bound xs ⟨sort, deps⟩ :: gs, bound, names, passes => by
      by_cases cond : (⟨sort, deps⟩ : Typ).deps = [] ∧
          (lookupSort env.sorts (⟨sort, deps⟩ : Typ).sort).map isUnstrict = some true
      · have passes' : afterBound env.sorts t xs gs bound names = true := by
          unfold afterBound
          unfold afterGroups at passes
          simp only [checkGroups, if_pos cond] at passes
          cases declared : declareBound xs bound names with
          | none => rw [declared] at passes; cases passes
          | some state => rw [declared] at passes; exact passes
        obtain ⟨noDeps, unstrict⟩ := cond
        dsimp only at noDeps unstrict
        subst noDeps
        obtain ⟨m, looked⟩ : ∃ m, lookupSort env.sorts sort = some m := by
          cases found : lookupSort env.sorts sort with
          | none => rw [found] at unstrict; cases unstrict
          | some m => exact ⟨m, rfl⟩
        rw [looked] at unstrict
        obtain ⟨p, pr, f, rfl⟩ := isUnstrict_iff.mp (Option.some.inj unstrict)
        have known := (sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩)
          (localsIn_term shape t.name bound names)).mpr (mem_of_lookupSort looked)
        have first := boundGroup_fires t.name (idsTree xs) sort (groupsTree gs) (arrowTree t.args t.ret) restTree
          p pr f _ known
        obtain ⟨bound', names', runs⟩ := bound_names_runs t restTree env old shape fresh sort gs
          (groups_runs t restTree env old shape fresh gs) xs bound names passes'
        exact ⟨bound', names', .step first runs⟩
      · unfold afterGroups at passes
        simp only [checkGroups, if_neg cond] at passes
        cases passes
  | .regular xs ty :: gs, bound, names, passes => by
      by_cases cond : (lookupSort env.sorts ty.sort).isSome ∧ depsBound bound ty.deps = true
      · have passes' : afterRegular env.sorts t xs gs bound names = true := by
          unfold afterRegular
          unfold afterGroups at passes
          simp only [checkGroups, if_pos cond] at passes
          cases declared : declareRegular xs names with
          | none => rw [declared] at passes; cases passes
          | some names'' => rw [declared] at passes; exact passes
        obtain ⟨declaredSort, allBound⟩ := cond
        obtain ⟨m, looked⟩ := Option.isSome_iff_exists.mp declaredSort
        have known := (sortEntry_mem (env := ⟨env.sorts, t.name :: env.terms⟩)
          (localsIn_term shape t.name bound names)).mpr (mem_of_lookupSort looked)
        have first := regularGroup_fires t.name (bidsTree xs) ty.sort (idsTree ty.deps) (groupsTree gs)
          (arrowTree t.args t.ret) restTree m _ known
        obtain ⟨bound', names', runs⟩ := regular_names_runs t restTree env old shape fresh gs
          (groups_runs t restTree env old shape fresh gs) xs bound names passes'
        exact ⟨bound', names', .step first (multiStep_append
          (deps_runs_regular t restTree env old bound names shape fresh xs gs ty.deps allBound) runs)⟩
      · unfold afterGroups at passes
        simp only [checkGroups, if_neg cond] at passes
        cases passes

theorem runs_of_checkAll : ∀ (ss : List Statement) (env env' : Env) (old : List Expr), LocalsIn env.terms old →
    (env.sorts.map Prod.fst).Nodup → checkAll env ss = some env' →
    ∃ old', (rewritingNone program).MultiStep
      ((([pending (fileTree (ss.map Statement.tree))] : List Expr) : Multiset Expr) + storeBag env old)
      ((([accepted] : List Expr) : Multiset Expr) + storeBag env' old')
  | [], env, env', old, _, _, done => by
      cases done
      exact ⟨old, .step (acceptFile_fires _) (.refl _)⟩
  | s :: ss, env, env', old, shape, nodup, done => by
      rw [show checkAll env (s :: ss) = (checkStatement env s).bind (fun e => checkAll e ss) from rfl] at done
      cases checked : checkStatement env s with
      | none =>
          rw [checked] at done
          cases done
      | some env'' =>
          rw [checked] at done
          have nodup'' := checkStatement_nodup nodup checked
          cases s with
          | sort d =>
              cases found : lookupSort env.sorts d.name with
              | none =>
                  have fresh : checkStatement env (.sort d) =
                      some ⟨(d.name, d.mods) :: env.sorts, env.terms⟩ := by
                    simp [checkStatement, declare, found]
                  rw [fresh] at checked
                  cases checked
                  have unnamed : sortName d.name ∉ (([pending (node "file_more" [node "statement_sort"
                      [d.pure, d.strict, d.provable, d.free, d.name], fileTree (ss.map Statement.tree)])] :
                      List Expr) : Multiset Expr) + storeBag env old := by
                    intro inside
                    rcases mem_one_add.mp inside with same | there
                    · exact absurd (row_inj.mp same).1 (by decide)
                    · exact lookupSort_eq_none_iff.mp found ((sortName_mem shape).mp there)
                  have first := declareSort_fires d.pure d.strict d.provable d.free d.name
                    (fileTree (ss.map Statement.tree)) (storeBag env old) unnamed
                  rw [declared_store] at first
                  obtain ⟨old', rest⟩ :=
                    runs_of_checkAll ss ⟨(d.name, d.mods) :: env.sorts, env.terms⟩ env' old shape nodup'' done
                  exact ⟨old', .step first rest⟩
              | some m =>
                  by_cases same : m = d.mods
                  · have again : checkStatement env (.sort d) = some ⟨env.sorts, env.terms⟩ := by
                      simp [checkStatement, declare, found, same]
                    rw [again] at checked
                    cases checked
                    have known : sortEntry d.name d.mods ∈ storeBag env old := by
                      rw [← same]
                      exact (sortEntry_mem shape).mpr (mem_of_lookupSort found)
                    obtain ⟨old', rest⟩ := runs_of_checkAll ss ⟨env.sorts, env.terms⟩ env' old shape nodup'' done
                    exact ⟨old', .step (repeatSort_fires d.pure d.strict d.provable d.free d.name
                      (fileTree (ss.map Statement.tree)) (storeBag env old) known) rest⟩
                  · have refused : checkStatement env (.sort d) = none := by
                      simp [checkStatement, declare, found, same]
                    rw [refused] at checked
                    cases checked
          | term t =>
              rw [show checkStatement env (.term t) = checkTerm env t from rfl] at checked
              unfold checkTerm at checked
              split at checked
              · rename_i conditions
                cases checked
                obtain ⟨unnamed, passes⟩ := conditions
                have freshTerm : termName t.name ∉ (([pending (node "file_more" [t.tree,
                    fileTree (ss.map Statement.tree)])] : List Expr) : Multiset Expr) + storeBag env old := by
                  intro inside
                  rcases mem_one_add.mp inside with same | there
                  · exact absurd (row_inj.mp same).1 (by decide)
                  · exact unnamed ((termName_mem shape).mp there)
                have first := startTerm_fires t.name (groupsTree t.groups) (arrowTree t.args t.ret)
                  (fileTree (ss.map Statement.tree)) (storeBag env old) freshTerm
                rw [named_store] at first
                obtain ⟨bound', names', runs⟩ :=
                  groups_runs t (fileTree (ss.map Statement.tree)) env old shape unnamed t.groups [] [] passes
                obtain ⟨old', rest⟩ := runs_of_checkAll ss ⟨env.sorts, t.name :: env.terms⟩ env'
                  (old ++ current t.name bound' names')
                  (localsIn_term shape t.name bound' names') nodup'' done
                exact ⟨old', .step first (multiStep_append runs rest)⟩
              · cases checked

/-! ## The theorem -/

/-- **A file of sort and term declarations reaches `accepted` exactly when MM0's rules accept it**, by rewriting of
bags with none queries. -/
theorem accepted_reachable_iff (ss : List Statement) :
    (∃ bag : Multiset Expr, (rewritingNone program).MultiStep (start ss) bag ∧ accepted ∈ bag) ↔
      (checkAll empty ss).isSome := by
  constructor
  · rintro ⟨bag, steps, inside⟩
    exact accepted_of_phase (phase_multi steps (phase_start ss)) inside
  · intro checked
    obtain ⟨env, done⟩ := Option.isSome_iff_exists.mp checked
    obtain ⟨old', runs⟩ := runs_of_checkAll ss empty env [] (fun e inside => absurd inside List.not_mem_nil)
      List.nodup_nil done
    refine ⟨(([accepted] : List Expr) : Multiset Expr) + storeBag env old', ?_, mem_one_add.mpr (Or.inl rfl)⟩
    rw [storeBag_empty, add_zero] at runs
    exact runs

/-- **On the step**: from every state that reads as the bag of a file of sort and term declarations, the step
reaches a state that reads as a bag holding `accepted` exactly when MM0's rules accept the file. -/
theorem on_the_step {O : Type uO} [DecidableEq O] [Infinite O] (ss : List Statement) {s : SState O}
    (reads : ReadsBag s (start ss)) :
    (∃ s', (stepSystem O program).MultiStep s s' ∧ ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag) ↔
      (checkAll empty ss).isSome :=
  (reachable_iff_none program_fragment (fun bag => accepted ∈ bag) reads).symm.trans (accepted_reachable_iff ss)

theorem start_reads (ss : List Statement) :
    ReadsBag (listState [pending (fileTree (ss.map Statement.tree))]) (start ss) :=
  listState_reads _

/-! ## Examples from MM0's test files -/

namespace Examples

open SortDeclarations.Examples (ident sortStmt)

/-- **Accepted on the step**: the state of the file's row reaches a state that reads as a bag holding
`accepted`. -/
def AcceptedOnTheStep (ss : List Statement) : Prop :=
  ∃ s', (stepSystem ℕ program).MultiStep (listState [pending (fileTree (ss.map Statement.tree))]) s' ∧
    ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag

theorem accepted_on_the_step_iff (ss : List Statement) : AcceptedOnTheStep ss ↔ (checkAll empty ss).isSome :=
  on_the_step ss (start_reads ss)

/-- A type without dependencies. -/
def plain (s : String) : Typ := ⟨ident s, []⟩

/-- `term_environment_positive.mm0`: `sort set; strict provable sort wff; term all {x: set} (ph: wff x): wff;
term imp: wff > wff > wff;`. -/
def positive : List Statement :=
  [.sort (sortStmt false false false false "set"), .sort (sortStmt false true true false "wff"),
    .term ⟨ident "all", [.bound [ident "x"] (plain "set"), .regular [some (ident "ph")] ⟨ident "wff", [ident "x"]⟩],
      [], plain "wff"⟩,
    .term ⟨ident "imp", [], [plain "wff", plain "wff"], plain "wff"⟩]

/-- `term_environment_bound_positive.mm0`: `sort set; strict provable sort wff; term all {x: set}: wff;`. -/
def boundPositive : List Statement :=
  [.sort (sortStmt false false false false "set"), .sort (sortStmt false true true false "wff"),
    .term ⟨ident "all", [.bound [ident "x"] (plain "set")], [], plain "wff"⟩]

/-- `term_environment_dependency_positive.mm0`: `sort set; strict provable sort wff;
term all {x: set} (ph: wff x): wff;`. -/
def dependencyPositive : List Statement :=
  [.sort (sortStmt false false false false "set"), .sort (sortStmt false true true false "wff"),
    .term ⟨ident "all", [.bound [ident "x"] (plain "set"), .regular [some (ident "ph")] ⟨ident "wff", [ident "x"]⟩],
      [], plain "wff"⟩]

/-- `term_environment_arrow_positive.mm0`: `strict provable sort wff; term imp: wff > wff > wff;`. -/
def arrowPositive : List Statement :=
  [.sort (sortStmt false true true false "wff"), .term ⟨ident "imp", [], [plain "wff", plain "wff"], plain "wff"⟩]

/-- `term_environment_constant_positive.mm0`: `sort value; term constant: value;`. -/
def constantPositive : List Statement :=
  [.sort (sortStmt false false false false "value"), .term ⟨ident "constant", [], [], plain "value"⟩]

/-- `term_environment_pure_target.mm0`: `pure sort set; term constant: set;`. -/
def pureTarget : List Statement :=
  [.sort (sortStmt true false false false "set"), .term ⟨ident "constant", [], [], plain "set"⟩]

/-- `term_environment_redeclaration.mm0`: `sort value; term constant: value; term constant: value;`. -/
def redeclaration : List Statement :=
  [.sort (sortStmt false false false false "value"), .term ⟨ident "constant", [], [], plain "value"⟩,
    .term ⟨ident "constant", [], [], plain "value"⟩]

/-- `term_environment_strict_binder.mm0`: `strict sort atom; sort result; term bind {x: atom}: result;`. -/
def strictBinder : List Statement :=
  [.sort (sortStmt false true false false "atom"), .sort (sortStmt false false false false "result"),
    .term ⟨ident "bind", [.bound [ident "x"] (plain "atom")], [], plain "result"⟩]

/-- `term_environment_unknown_dependency.mm0`: `sort set; sort wff; term bad (ph: wff x): wff;`. -/
def unknownDependency : List Statement :=
  [.sort (sortStmt false false false false "set"), .sort (sortStmt false false false false "wff"),
    .term ⟨ident "bad", [.regular [some (ident "ph")] ⟨ident "wff", [ident "x"]⟩], [], plain "wff"⟩]

/-- `term_environment_unknown_sort.mm0`: `term constant: missing;`. -/
def unknownSort : List Statement := [.term ⟨ident "constant", [], [], plain "missing"⟩]

/-- A control beside the test files: a binder name used twice in one term, `term twice {x: set} (x: wff): wff;`. -/
def duplicateBinder : List Statement :=
  [.sort (sortStmt false false false false "set"), .sort (sortStmt false false false false "wff"),
    .term ⟨ident "twice", [.bound [ident "x"] (plain "set"), .regular [some (ident "x")] (plain "wff")], [],
      plain "wff"⟩]

theorem positive_accepted : AcceptedOnTheStep positive :=
  (accepted_on_the_step_iff _).mpr (by decide +kernel)

theorem boundPositive_accepted : AcceptedOnTheStep boundPositive :=
  (accepted_on_the_step_iff _).mpr (by decide +kernel)

theorem dependencyPositive_accepted : AcceptedOnTheStep dependencyPositive :=
  (accepted_on_the_step_iff _).mpr (by decide +kernel)

theorem arrowPositive_accepted : AcceptedOnTheStep arrowPositive :=
  (accepted_on_the_step_iff _).mpr (by decide +kernel)

theorem constantPositive_accepted : AcceptedOnTheStep constantPositive :=
  (accepted_on_the_step_iff _).mpr (by decide +kernel)

theorem pureTarget_refused : ¬ AcceptedOnTheStep pureTarget := by
  rw [accepted_on_the_step_iff]
  decide +kernel

theorem redeclaration_refused : ¬ AcceptedOnTheStep redeclaration := by
  rw [accepted_on_the_step_iff]
  decide +kernel

theorem strictBinder_refused : ¬ AcceptedOnTheStep strictBinder := by
  rw [accepted_on_the_step_iff]
  decide +kernel

theorem unknownDependency_refused : ¬ AcceptedOnTheStep unknownDependency := by
  rw [accepted_on_the_step_iff]
  decide +kernel

theorem unknownSort_refused : ¬ AcceptedOnTheStep unknownSort := by
  rw [accepted_on_the_step_iff]
  decide +kernel

theorem duplicateBinder_refused : ¬ AcceptedOnTheStep duplicateBinder := by
  rw [accepted_on_the_step_iff]
  decide +kernel

end Examples

#print axioms phase_step
#print axioms groups_runs
#print axioms runs_of_checkAll
#print axioms accepted_reachable_iff
#print axioms on_the_step
#print axioms Examples.positive_accepted
#print axioms Examples.boundPositive_accepted
#print axioms Examples.dependencyPositive_accepted
#print axioms Examples.arrowPositive_accepted
#print axioms Examples.constantPositive_accepted
#print axioms Examples.pureTarget_refused
#print axioms Examples.redeclaration_refused
#print axioms Examples.strictBinder_refused
#print axioms Examples.unknownDependency_refused
#print axioms Examples.unknownSort_refused
#print axioms Examples.duplicateBinder_refused

end Mettapedia.Languages.MM0.OnTheStep.TermDeclarations
