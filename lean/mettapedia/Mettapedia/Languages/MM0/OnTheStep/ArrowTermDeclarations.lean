import Mettapedia.Languages.MM0.OnTheStep.SortDeclarations

/-!
# Files of sort declarations and of term declarations without binders

The theorem of `SortDeclarations`, extended to files whose statements are sort declarations and term
declarations whose type is an arrow of sorts without dependencies and that have no binder groups:
`term imp: wff > wff > wff;`, `term constant: value;`. The program is `DeclarationProgram.program`, all twenty
rules; the environment in the store holds the sort rows and one row per declared term name.

* **MM0's rules** (`checkStatement`, `checkAll`), written by hand after MM0's GSLT definition
  (`term_environment_v1`), with no mechanical link to that file proved: a
  term's name is no term's name; every argument sort is a declared sort; the return sort is a declared sort that
  is not `pure`; sorts as in `SortDeclarations.declare`.
* **The theorem** (`accepted_reachable_iff`, `on_the_step`): from the bag of such a file, rewriting of bags with
  the none query reaches a bag holding `accepted` exactly when MM0's rules accept the file; on the step, for every state
  that reads as the file's bag. The invariant (`Phase`) has three forms: the cursor at the rest of the file; a term
  under check (its name row made, its binders done, a prefix of its argument sorts checked, or its return sort
  checked); `accepted`.
* **Examples from MM0's test files** (`Examples`, CeTTa's `tests/langdef/mm0/`):
  `term_environment_arrow_positive.mm0` and `term_environment_constant_positive.mm0` are accepted on the step;
  `term_environment_pure_target.mm0`, `term_environment_redeclaration.mm0` and
  `term_environment_unknown_sort.mm0` are refused: no run reaches `accepted`.

The general case, with binder groups (`{x: set}`, `(ph: wff x)`) and dependencies, is `TermDeclarations`; the
theorem here is its special case for terms without binders, kept for the helpers `TermDeclarations` uses
(`isTarget`, `multiStep_append`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.ArrowTermDeclarations

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
  declare_nodup mem_one_add declared_bag)

universe uO

/-! ## Statements -/

/-- The tree of a type of a sort without dependencies. -/
def typTree (s : Expr) : Expr := node "typ_deps" [s, node "ids_empty" []]

/-- The tree of an arrow type: argument sorts, then the return sort. -/
def arrowTree : List Expr → Expr → Expr
  | [], r => node "arrow_last" [typTree r]
  | a :: as, r => node "arrow_more" [typTree a, arrowTree as r]

/-- **A term statement without binders and without dependencies**: `term t: s₁ > … > sₙ > r;`. -/
structure ArrowTerm where
  name : Expr
  args : List Expr
  ret : Expr

/-- The tree of the statement (`statement_term` with no binder group). -/
def ArrowTerm.tree (t : ArrowTerm) : Expr :=
  node "statement_term" [t.name, node "tbinders_empty" [], arrowTree t.args t.ret]

/-- **A statement of the fragment**: a sort declaration or a term declaration without binders. -/
inductive Statement where
  | sort (d : SortStatement)
  | term (t : ArrowTerm)

/-- The tree of a statement. -/
def Statement.tree : Statement → Expr
  | .sort d => d.tree
  | .term t => t.tree

/-! ## MM0's rules -/

/-- **An environment**: the declared sorts with their modifiers, and the declared term names. -/
structure Env where
  sorts : SortEnv
  terms : List Expr

/-- The second of four modifiers. -/
def secondOf : Expr → Expr
  | .app _ (.app b _) => b
  | _ => .sym 0

/-- The third of four modifiers. -/
def thirdOf : Expr → Expr
  | .app _ (.app _ (.app c _)) => c
  | _ => .sym 0

/-- The fourth of four modifiers. -/
def fourthOf : Expr → Expr
  | .app _ (.app _ (.app _ (.app d _))) => d
  | _ => .sym 0

/-- **The modifiers of a sort that is not `pure`**: four modifiers whose first is `pure_no`. -/
def isTarget (m : Expr) : Bool :=
  decide (m = modifiers (node "pure_no" []) (secondOf m) (thirdOf m) (fourthOf m))

/-- **MM0's rules for a term declaration without binders**: its name is no term's; every argument sort is
declared; the return sort is declared and not `pure`. -/
def checkTerm (env : Env) (t : ArrowTerm) : Option Env :=
  if t.name ∉ env.terms ∧ (∀ a ∈ t.args, (lookupSort env.sorts a).isSome) ∧
      (lookupSort env.sorts t.ret).map isTarget = some true then
    some ⟨env.sorts, t.name :: env.terms⟩
  else none

/-- MM0's rule for one statement. -/
def checkStatement (env : Env) : Statement → Option Env
  | .sort d => (declare env.sorts d).map fun sorts => ⟨sorts, env.terms⟩
  | .term t => checkTerm env t

/-- **MM0's rules for a file of statements**, in order. -/
def checkAll : Env → List Statement → Option Env
  | env, [] => some env
  | env, s :: ss => (checkStatement env s).bind fun env' => checkAll env' ss

/-- The empty environment. -/
def empty : Env := ⟨[], []⟩

/-! ## Bags -/

/-- The rows of an environment: the sort rows and a name row per declared term. -/
def envRows' (env : Env) : List Expr := envRows env.sorts ++ env.terms.map termName

/-- The bag of an environment. -/
abbrev envBag (env : Env) : Multiset Expr := (envRows' env : Multiset Expr)

/-- **The bag of a file**: its cursor row alone. -/
def start (ss : List Statement) : Multiset Expr :=
  (([pending (fileTree (ss.map Statement.tree))] : List Expr) : Multiset Expr)

theorem mem_envRows' {e : Expr} {env : Env} (inside : e ∈ envRows' env) :
    e ∈ envRows env.sorts ∨ ∃ t ∈ env.terms, e = termName t := by
  rcases List.mem_append.mp inside with sorted | named
  · exact Or.inl sorted
  · obtain ⟨t, member, rfl⟩ := List.mem_map.mp named
    exact Or.inr ⟨t, member, rfl⟩

theorem kind_of_mem_envRows' {e : Expr} {env : Env} (inside : e ∈ envRows' env) :
    kindOf e = some 1 ∨ kindOf e = some 2 ∨ kindOf e = some 3 := by
  rcases mem_envRows' inside with sorted | ⟨t, -, rfl⟩
  · rcases SortDeclarations.kind_of_mem_envRows sorted with one | two
    · exact Or.inl one
    · exact Or.inr (Or.inl two)
  · exact Or.inr (Or.inr rfl)

theorem termName_mem_envRows' {t : Expr} {env : Env} : termName t ∈ envRows' env ↔ t ∈ env.terms := by
  constructor
  · intro inside
    rcases mem_envRows' inside with sorted | ⟨t', member, same⟩
    · rcases SortDeclarations.kind_of_mem_envRows sorted with one | two
      · simp [termName] at one
      · simp [termName] at two
    · rw [(List.cons.inj (row_inj.mp same).2).1]
      exact member
  · intro member
    exact List.mem_append_right _ (List.mem_map_of_mem member)

theorem sortName_mem_envRows' {s : Expr} {env : Env} :
    sortName s ∈ envRows' env ↔ s ∈ env.sorts.map Prod.fst := by
  constructor
  · intro inside
    rcases mem_envRows' inside with sorted | ⟨t, -, same⟩
    · exact sortName_mem_envRows.mp sorted
    · exact absurd (row_inj.mp same).1 (by decide)
  · exact fun member => List.mem_append_left _ (sortName_mem_envRows.mpr member)

theorem sortEntry_mem_envRows' {s m : Expr} {env : Env} :
    sortEntry s m ∈ envRows' env ↔ (s, m) ∈ env.sorts := by
  constructor
  · intro inside
    rcases mem_envRows' inside with sorted | ⟨t, -, same⟩
    · exact sortEntry_mem_envRows.mp sorted
    · exact absurd (row_inj.mp same).1 (by decide)
  · exact fun member => List.mem_append_left _ (sortEntry_mem_envRows.mpr member)

/-- **A rule that does not take an environment row takes the row beside the environment.** -/
theorem take_inv {θ : ℕ → Expr} {k : ℕ} {args : List Tm} {rest : Multiset Expr} {c : Expr} {env : Env}
    (split : (([inst θ (rowP k args)] : List Expr) : Multiset Expr) + rest =
      (([c] : List Expr) : Multiset Expr) + envBag env) (notEnv : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3) :
    row k (args.map (inst θ)) = c ∧ rest = envBag env := by
  have inside : inst θ (rowP k args) ∈ (([c] : List Expr) : Multiset Expr) + envBag env := by
    rw [← split]
    exact mem_one_add.mpr (Or.inl rfl)
  rw [inst_rowP] at inside
  rcases mem_one_add.mp inside with same | there
  · refine ⟨same, ?_⟩
    rw [inst_rowP, same] at split
    exact add_left_cancel split
  · have kinds := kind_of_mem_envRows' (Multiset.mem_coe.mp there)
    rw [kindOf_row] at kinds
    rcases kinds with same | same | same <;> (simp only [Option.some.injEq] at same; omega)

theorem declared_bag' (s m r : Expr) (env : Env) :
    (([sortName s, sortEntry s m, pending r] : List Expr) : Multiset Expr) + envBag env =
      (([pending r] : List Expr) : Multiset Expr) + envBag ⟨(s, m) :: env.sorts, env.terms⟩ := by
  simp only [envBag, envRows', envRows, List.cons_append, ← Multiset.cons_coe, Multiset.cons_add,
    Multiset.coe_nil, zero_add]
  rw [Multiset.cons_swap (pending r) (sortName s), Multiset.cons_swap (pending r) (sortEntry s m)]

theorem named_bag (t c : Expr) (env : Env) :
    (([termName t, c] : List Expr) : Multiset Expr) + envBag env =
      (([c] : List Expr) : Multiset Expr) + envBag ⟨env.sorts, t :: env.terms⟩ := by
  have middle : ((envRows' ⟨env.sorts, t :: env.terms⟩ : List Expr) : Multiset Expr) =
      termName t ::ₘ (envRows' env : Multiset Expr) := by
    rw [Multiset.cons_coe]
    exact Multiset.coe_eq_coe.mpr (List.perm_middle (l₁ := envRows env.sorts) (l₂ := env.terms.map termName))
  simp only [envBag, middle, ← Multiset.cons_coe, Multiset.cons_add, Multiset.coe_nil, zero_add]
  rw [Multiset.cons_swap]

/-! ## Inversions -/

theorem statement_cases {x : Expr} {s : Statement} {ss : List Statement} {g : Expr}
    (same : node "file_more" [x, g] = fileTree ((s :: ss).map Statement.tree)) :
    x = s.tree ∧ g = fileTree (ss.map Statement.tree) := by
  obtain ⟨first, rest⟩ := List.cons.inj (node_inj.mp same).2
  exact ⟨first, (List.cons.inj rest).1⟩

theorem arrow_more_inv {x y z r : Expr} {post : List Expr}
    (same : node "arrow_more" [node "typ_deps" [x, y], z] = arrowTree post r) :
    ∃ a post', post = a :: post' ∧ x = a ∧ y = node "ids_empty" [] ∧ z = arrowTree post' r := by
  cases post with
  | nil => exact absurd (node_inj.mp same).1 (by decide)
  | cons a post' =>
      obtain ⟨typ, rest⟩ := List.cons.inj (node_inj.mp same).2
      obtain ⟨sameSort, deps⟩ := List.cons.inj (node_inj.mp typ).2
      exact ⟨a, post', rfl, sameSort, (List.cons.inj deps).1, (List.cons.inj rest).1⟩

theorem arrow_last_inv {x y r : Expr} {post : List Expr}
    (same : node "arrow_last" [node "typ_deps" [x, y]] = arrowTree post r) :
    post = [] ∧ x = r ∧ y = node "ids_empty" [] := by
  cases post with
  | nil =>
      obtain ⟨typ, -⟩ := List.cons.inj (node_inj.mp same).2
      obtain ⟨sameSort, deps⟩ := List.cons.inj (node_inj.mp typ).2
      exact ⟨rfl, sameSort, (List.cons.inj deps).1⟩
  | cons a post' => exact absurd (node_inj.mp same).1 (by decide)

theorem isTarget_iff {m : Expr} : isTarget m = true ↔ ∃ st pr f, m = modifiers (node "pure_no" []) st pr f := by
  constructor
  · intro target
    exact ⟨_, _, _, of_decide_eq_true target⟩
  · rintro ⟨st, pr, f, rfl⟩
    exact decide_eq_true rfl

/-! ## The invariant of every run -/

/-- **Where the check of a term can be**: its binders not yet passed; a prefix of its argument sorts checked, at
the next argument type or at the dependencies of the last one; or every argument and the return sort checked, at
the return type's dependencies. -/
def InTerm (env : Env) (t : ArrowTerm) (restTree cursor : Expr) : Prop :=
  cursor = binders t.name (node "tbinders_empty" []) (arrowTree t.args t.ret) restTree ∨
    (∃ pre post, t.args = pre ++ post ∧ (∀ a ∈ pre, (lookupSort env.sorts a).isSome) ∧
      (cursor = arrow t.name (arrowTree post t.ret) restTree ∨
        cursor = arrowDeps t.name (node "ids_empty" []) (arrowTree post t.ret) restTree)) ∨
    ((∀ a ∈ t.args, (lookupSort env.sorts a).isSome) ∧ (lookupSort env.sorts t.ret).map isTarget = some true ∧
      cursor = returnDeps t.name (node "ids_empty" []) restTree)

/-- **Where a run from a file of the fragment can be.** -/
def Phase (ss₀ : List Statement) (bag : Multiset Expr) : Prop :=
  (∃ done rest env, ss₀ = done ++ rest ∧ checkAll empty done = some env ∧
      bag = (([pending (fileTree (rest.map Statement.tree))] : List Expr) : Multiset Expr) + envBag env) ∨
    (∃ done t rest env cursor, ss₀ = done ++ .term t :: rest ∧ checkAll empty done = some env ∧
      t.name ∉ env.terms ∧ InTerm env t (fileTree (rest.map Statement.tree)) cursor ∧
      bag = (([cursor] : List Expr) : Multiset Expr) + envBag ⟨env.sorts, t.name :: env.terms⟩) ∨
    (∃ env, checkAll empty ss₀ = some env ∧ bag = (([accepted] : List Expr) : Multiset Expr) + envBag env)

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

theorem phase_start (ss₀ : List Statement) : Phase ss₀ (start ss₀) :=
  Or.inl ⟨[], ss₀, empty, rfl, rfl, (add_zero _).symm⟩

/-- **Every rewrite keeps the invariant.** -/
theorem phase_step {ss₀ : List Statement} {bag bag' : Multiset Expr} (phase : Phase ss₀ bag)
    (step : RewritesNone program bag bag') : Phase ss₀ bag' := by
  obtain ⟨r, member, θ, rest, split, readsIn, -, nones, rfl⟩ := step
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases phase with ⟨done, rest₀, env, decomposed, checked, rfl⟩ |
    ⟨done, t, rest₀, env, cursor, decomposed, checked, fresh, inTerm, rfl⟩ | ⟨env, checked, rfl⟩
  · -- the cursor at the rest of the file
    have nodup := checkAll_nodup (env := empty) List.nodup_nil checked
    rcases member with rfl | rfl | rfl | rfl | member
    · -- declareSort
      obtain ⟨same, rfl⟩ := take_inv split (by decide)
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
                  Statement.tree))] : List Expr) : Multiset Expr) + envBag env :=
                nones (rowP 1 [u 4]) (List.mem_singleton_self _)
              have looked : lookupSort env.sorts d.name = none := lookupSort_eq_none_iff.mpr fun known =>
                freshSort (mem_one_add.mpr (Or.inr (by
                  rw [hs]
                  exact Multiset.mem_coe.mpr (sortName_mem_envRows'.mpr known))))
              have declared : checkStatement env (.sort d) = some ⟨(d.name, d.mods) :: env.sorts, env.terms⟩ := by
                simp [checkStatement, declare, looked]
              refine Or.inl ⟨done ++ [.sort d], ss, ⟨(d.name, d.mods) :: env.sorts, env.terms⟩,
                by rw [decomposed, List.append_assoc, List.singleton_append],
                by rw [checkAll_append, checked]; exact declared, ?_⟩
              show (([sortName (θ 4), sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)), pending (θ 5)] :
                  List Expr) : Multiset Expr) + envBag env = _
              rw [hp, hst, hpr, hf, hs, hr]
              exact declared_bag' _ _ _ env
    · -- repeatSort
      obtain ⟨same, rfl⟩ := take_inv split (by decide)
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
              have known : sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)) ∈ envBag env :=
                readsIn (rowP 2 [u 4, listP [u 0, u 1, u 2, u 3]]) (List.mem_singleton_self _)
              rw [hp, hst, hpr, hf, hs] at known
              have entered : (d.name, d.mods) ∈ env.sorts := sortEntry_mem_envRows'.mp (Multiset.mem_coe.mp known)
              have declared : checkStatement env (.sort d) = some ⟨env.sorts, env.terms⟩ := by
                simp [checkStatement, declare, lookupSort_of_mem nodup entered]
              refine Or.inl ⟨done ++ [.sort d], ss, env, by rw [decomposed, List.append_assoc, List.singleton_append],
                by rw [checkAll_append, checked]; exact declared, ?_⟩
              show (([pending (θ 5)] : List Expr) : Multiset Expr) + envBag env = _
              rw [hr]
    · -- acceptFile
      obtain ⟨same, rfl⟩ := take_inv split (by decide)
      have file : node "file_empty" [] = fileTree (rest₀.map Statement.tree) := (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil => exact Or.inr (Or.inr ⟨env, by rw [decomposed, List.append_nil]; exact checked, rfl⟩)
      | cons s ss => exact absurd (node_inj.mp file).1 (by decide)
    · -- startTerm
      obtain ⟨same, rfl⟩ := take_inv split (by decide)
      have file : node "file_more" [node "statement_term" [θ 0, θ 1, θ 2], θ 3] =
          fileTree (rest₀.map Statement.tree) := (List.cons.inj (row_inj.mp same).2).1
      cases rest₀ with
      | nil => exact absurd (node_inj.mp file).1 (by decide)
      | cons s ss =>
          obtain ⟨statement, hr⟩ := statement_cases file
          cases s with
          | sort d => exact absurd (node_inj.mp statement).1 (by decide)
          | term t =>
              have fields := (node_inj.mp statement).2
              obtain ⟨hn, fields⟩ := List.cons.inj fields
              obtain ⟨hb, fields⟩ := List.cons.inj fields
              obtain ⟨ha, -⟩ := List.cons.inj fields
              have freshTerm : termName (θ 0) ∉ (([pending (fileTree ((Statement.term t :: ss).map
                  Statement.tree))] : List Expr) : Multiset Expr) + envBag env :=
                nones (rowP 3 [u 0]) (List.mem_singleton_self _)
              have unnamed : t.name ∉ env.terms := fun known =>
                freshTerm (mem_one_add.mpr (Or.inr (by
                  rw [hn]
                  exact Multiset.mem_coe.mpr (termName_mem_envRows'.mpr known))))
              refine Or.inr (Or.inl ⟨done, t, ss, env, binders t.name (node "tbinders_empty" [])
                (arrowTree t.args t.ret) (fileTree (ss.map Statement.tree)), decomposed, checked, unnamed,
                Or.inl rfl, ?_⟩)
              show (([termName (θ 0), binders (θ 0) (θ 1) (θ 2) (θ 3)] : List Expr) : Multiset Expr) +
                envBag env = _
              rw [hn, hb, ha, hr]
              exact named_bag _ _ env
    · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))
  · -- a term under check
    rcases inTerm with rfl | ⟨pre, post, split₀, checkedPre, rfl | rfl⟩ | ⟨checkedArgs, target, rfl⟩
    · -- binders not yet passed: only bindersDone
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))
        | skip
      · -- boundGroup
        obtain ⟨same, -⟩ := take_inv split (by decide)
        have groups := (List.cons.inj (List.cons.inj (row_inj.mp same).2).2).1
        rw [inst_nodeP] at groups
        exact absurd (node_inj.mp groups).1 (by decide)
      · -- regularGroup
        obtain ⟨same, -⟩ := take_inv split (by decide)
        have groups := (List.cons.inj (List.cons.inj (row_inj.mp same).2).2).1
        rw [inst_nodeP] at groups
        exact absurd (node_inj.mp groups).1 (by decide)
      · -- bindersDone
        obtain ⟨same, rfl⟩ := take_inv split (by decide)
        have parts : [θ 0, node "tbinders_empty" [], θ 1, θ 2] =
            [t.name, node "tbinders_empty" [], arrowTree t.args t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        refine Or.inr (Or.inl ⟨done, t, rest₀, env, arrow t.name (arrowTree t.args t.ret)
          (fileTree (rest₀.map Statement.tree)), decomposed, checked, fresh,
          Or.inr (Or.inl ⟨[], t.args, rfl, fun a inside => absurd inside List.not_mem_nil, Or.inl rfl⟩), ?_⟩)
        show (([arrow (θ 0) (θ 1) (θ 2)] : List Expr) : Multiset Expr) + _ = _
        rw [hn, hty, hr]
    · -- at an argument type or the return type
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))
        | skip
      · -- arrowArgument
        obtain ⟨same, rfl⟩ := take_inv split (by decide)
        have parts : [θ 0, node "arrow_more" [node "typ_deps" [θ 1, θ 2], θ 3], θ 4] =
            [t.name, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        obtain ⟨a, post', rfl, ha, hdeps, htail⟩ := arrow_more_inv hty
        have known : sortEntry (θ 1) (θ 5) ∈ envBag ⟨env.sorts, t.name :: env.terms⟩ :=
          readsIn (rowP 2 [u 1, u 5]) (List.mem_singleton_self _)
        rw [ha] at known
        have declaredA : (lookupSort env.sorts a).isSome := by
          have entered := sortEntry_mem_envRows'.mp (Multiset.mem_coe.mp known)
          rw [Option.isSome_iff_exists]
          exact ⟨_, lookupSort_of_mem (checkAll_nodup (env := empty) List.nodup_nil checked) entered⟩
        refine Or.inr (Or.inl ⟨done, t, rest₀, env, arrowDeps t.name (node "ids_empty" []) (arrowTree post' t.ret)
          (fileTree (rest₀.map Statement.tree)), decomposed, checked, fresh,
          Or.inr (Or.inl ⟨pre ++ [a], post', by rw [split₀, List.append_assoc, List.singleton_append],
            fun b inside => ?_, Or.inr rfl⟩), ?_⟩)
        · rcases List.mem_append.mp inside with early | last
          · exact checkedPre b early
          · rw [List.mem_singleton.mp last]
            exact declaredA
        · show (([arrowDeps (θ 0) (θ 2) (θ 3) (θ 4)] : List Expr) : Multiset Expr) + _ = _
          rw [hn, hdeps, htail, hr]
      · -- arrowReturn
        obtain ⟨same, rfl⟩ := take_inv split (by decide)
        have parts : [θ 0, node "arrow_last" [node "typ_deps" [θ 1, θ 2]], θ 3] =
            [t.name, arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨hty, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        obtain ⟨rfl, hret, hdeps⟩ := arrow_last_inv hty
        have known : sortEntry (θ 1) (modifiers (node "pure_no" []) (θ 4) (θ 5) (θ 6)) ∈
            envBag ⟨env.sorts, t.name :: env.terms⟩ :=
          readsIn (rowP 2 [u 1, listP [nodeP "pure_no" [], u 4, u 5, u 6]]) (List.mem_singleton_self _)
        rw [hret] at known
        have entered := sortEntry_mem_envRows'.mp (Multiset.mem_coe.mp known)
        have looked := lookupSort_of_mem (checkAll_nodup (env := empty) List.nodup_nil checked) entered
        refine Or.inr (Or.inl ⟨done, t, rest₀, env, returnDeps t.name (node "ids_empty" [])
          (fileTree (rest₀.map Statement.tree)), decomposed, checked, fresh,
          Or.inr (Or.inr ⟨fun b inside => checkedPre b (by rw [split₀, List.append_nil] at inside; exact inside),
            by rw [looked]; exact congrArg some (isTarget_iff.mpr ⟨_, _, _, rfl⟩), rfl⟩), ?_⟩)
        show (([returnDeps (θ 0) (θ 2) (θ 3)] : List Expr) : Multiset Expr) + _ = _
        rw [hn, hdeps, hr]
    · -- at the dependencies of the last argument type
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))
        | skip
      · -- arrowDep
        obtain ⟨same, -⟩ := take_inv split (by decide)
        have deps := (List.cons.inj (List.cons.inj (row_inj.mp same).2).2).1
        rw [inst_nodeP] at deps
        exact absurd (node_inj.mp deps).1 (by decide)
      · -- arrowDepsDone
        obtain ⟨same, rfl⟩ := take_inv split (by decide)
        have parts : [θ 0, node "ids_empty" [], θ 1, θ 2] =
            [t.name, node "ids_empty" [], arrowTree post t.ret, fileTree (rest₀.map Statement.tree)] :=
          (row_inj.mp same).2
        obtain ⟨hn, parts⟩ := List.cons.inj parts
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨htail, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        refine Or.inr (Or.inl ⟨done, t, rest₀, env, arrow t.name (arrowTree post t.ret)
          (fileTree (rest₀.map Statement.tree)), decomposed, checked, fresh,
          Or.inr (Or.inl ⟨pre, post, split₀, checkedPre, Or.inl rfl⟩), ?_⟩)
        show (([arrow (θ 0) (θ 1) (θ 2)] : List Expr) : Multiset Expr) + _ = _
        rw [hn, htail, hr]
    · -- at the return type's dependencies
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))
        | skip
      · -- returnDep
        obtain ⟨same, -⟩ := take_inv split (by decide)
        have deps := (List.cons.inj (List.cons.inj (row_inj.mp same).2).2).1
        rw [inst_nodeP] at deps
        exact absurd (node_inj.mp deps).1 (by decide)
      · -- returnDepsDone
        obtain ⟨same, rfl⟩ := take_inv split (by decide)
        have parts : [θ 0, node "ids_empty" [], θ 1] =
            [t.name, node "ids_empty" [], fileTree (rest₀.map Statement.tree)] := (row_inj.mp same).2
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨-, parts⟩ := List.cons.inj parts
        obtain ⟨hr, -⟩ := List.cons.inj parts
        have declared : checkStatement env (.term t) = some ⟨env.sorts, t.name :: env.terms⟩ := by
          show checkTerm env t = _
          unfold checkTerm
          rw [if_pos ⟨fresh, checkedArgs, target⟩]
        refine Or.inl ⟨done ++ [.term t], rest₀, ⟨env.sorts, t.name :: env.terms⟩,
          by rw [decomposed, List.append_assoc, List.singleton_append],
          by rw [checkAll_append, checked]; exact declared, ?_⟩
        show (([pending (θ 1)] : List Expr) : Multiset Expr) + _ = _
        rw [hr]
  · -- accepted: no rule takes
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      (obtain ⟨same, -⟩ := take_inv split (by decide); exact absurd (row_inj.mp same).1 (by decide))

theorem phase_multi {ss₀ : List Statement} : ∀ {bag bag' : (rewritingNone program).Term},
    (rewritingNone program).MultiStep bag bag' → Phase ss₀ bag → Phase ss₀ bag'
  | _, _, .refl _, phase => phase
  | _, _, .step first rest, phase => phase_multi rest (phase_step phase first)

theorem accepted_of_phase {ss₀ : List Statement} {bag : Multiset Expr} (phase : Phase ss₀ bag)
    (inside : accepted ∈ bag) : (checkAll empty ss₀).isSome := by
  rcases phase with ⟨done, rest, env, -, -, rfl⟩ | ⟨done, t, rest, env, cursor, -, -, -, inTerm, rfl⟩ |
    ⟨env, checked, -⟩
  · rcases mem_one_add.mp inside with same | there
    · exact absurd (row_inj.mp same).1 (by decide)
    · have kinds := kind_of_mem_envRows' (Multiset.mem_coe.mp there)
      simp [accepted] at kinds
  · rcases mem_one_add.mp inside with same | there
    · rcases inTerm with rfl | ⟨pre, post, -, -, rfl | rfl⟩ | ⟨-, -, rfl⟩ <;>
        exact absurd (row_inj.mp same).1 (by decide)
    · have kinds := kind_of_mem_envRows' (Multiset.mem_coe.mp there)
      simp [accepted] at kinds
  · simp [checked]

/-! ## The runs -/

theorem multiStep_append {S : GSLT.{0}} : ∀ {a b c : S.Term}, S.MultiStep a b → S.MultiStep b c → S.MultiStep a c
  | _, _, _, .refl _, second => second
  | _, _, _, .step first rest, second => .step first (multiStep_append rest second)

theorem arrow_runs (env : Env) (t : ArrowTerm) (restTree : Expr) :
    ∀ (post : List Expr), (∀ a ∈ post, (lookupSort env.sorts a).isSome) →
      (lookupSort env.sorts t.ret).map isTarget = some true →
      (rewritingNone program).MultiStep
        ((([arrow t.name (arrowTree post t.ret) restTree] : List Expr) : Multiset Expr) +
          envBag ⟨env.sorts, t.name :: env.terms⟩)
        ((([pending restTree] : List Expr) : Multiset Expr) + envBag ⟨env.sorts, t.name :: env.terms⟩)
  | [], _, target => by
      obtain ⟨m, looked⟩ : ∃ m, lookupSort env.sorts t.ret = some m := by
        cases found : lookupSort env.sorts t.ret with
        | none => rw [found] at target; cases target
        | some m => exact ⟨m, rfl⟩
      rw [looked] at target
      obtain ⟨st, pr, f, rfl⟩ := isTarget_iff.mp (Option.some.inj target)
      have known : sortEntry t.ret (modifiers (node "pure_no" []) st pr f) ∈
          envBag ⟨env.sorts, t.name :: env.terms⟩ :=
        Multiset.mem_coe.mpr (sortEntry_mem_envRows'.mpr (mem_of_lookupSort looked))
      exact .step (arrowReturn_fires t.name t.ret (node "ids_empty" []) restTree st pr f _ known)
        (.step (returnDepsDone_fires t.name restTree _) (.refl _))
  | a :: post, declaredAll, target => by
      obtain ⟨m, looked⟩ : ∃ m, lookupSort env.sorts a = some m := by
        have := declaredAll a List.mem_cons_self
        cases found : lookupSort env.sorts a with
        | none => rw [found] at this; cases this
        | some m => exact ⟨m, rfl⟩
      have known : sortEntry a m ∈ envBag ⟨env.sorts, t.name :: env.terms⟩ :=
        Multiset.mem_coe.mpr (sortEntry_mem_envRows'.mpr (mem_of_lookupSort looked))
      exact .step (arrowArgument_fires t.name a (node "ids_empty" []) (arrowTree post t.ret) restTree m _ known)
        (.step (arrowDepsDone_fires t.name (arrowTree post t.ret) restTree _)
          (arrow_runs env t restTree post (fun b inside => declaredAll b (List.mem_cons_of_mem _ inside)) target))

theorem runs_of_checkAll : ∀ (ss : List Statement) (env env' : Env), checkAll env ss = some env' →
    (rewritingNone program).MultiStep
      ((([pending (fileTree (ss.map Statement.tree))] : List Expr) : Multiset Expr) + envBag env)
      ((([accepted] : List Expr) : Multiset Expr) + envBag env')
  | [], env, env', done => by
      cases done
      exact .step (acceptFile_fires (envBag env)) (.refl _)
  | s :: ss, env, env', done => by
      rw [show checkAll env (s :: ss) = (checkStatement env s).bind (fun e => checkAll e ss) from rfl] at done
      cases checked : checkStatement env s with
      | none =>
          rw [checked] at done
          cases done
      | some env'' =>
          rw [checked] at done
          have rest := runs_of_checkAll ss env'' env' done
          cases s with
          | sort d =>
              cases found : lookupSort env.sorts d.name with
              | none =>
                  have fresh : checkStatement env (.sort d) = some ⟨(d.name, d.mods) :: env.sorts, env.terms⟩ := by
                    simp [checkStatement, declare, found]
                  rw [fresh] at checked
                  cases checked
                  have unnamed : sortName d.name ∉ (([pending (node "file_more" [node "statement_sort"
                      [d.pure, d.strict, d.provable, d.free, d.name], fileTree (ss.map Statement.tree)])] :
                      List Expr) : Multiset Expr) + envBag env := by
                    intro inside
                    rcases mem_one_add.mp inside with same | there
                    · exact absurd (row_inj.mp same).1 (by decide)
                    · exact lookupSort_eq_none_iff.mp found (sortName_mem_envRows'.mp (Multiset.mem_coe.mp there))
                  have first := declareSort_fires d.pure d.strict d.provable d.free d.name
                    (fileTree (ss.map Statement.tree)) (envBag env) unnamed
                  rw [declared_bag'] at first
                  exact .step first rest
              | some m =>
                  by_cases same : m = d.mods
                  · have again : checkStatement env (.sort d) = some ⟨env.sorts, env.terms⟩ := by
                      simp [checkStatement, declare, found, same]
                    rw [again] at checked
                    cases checked
                    have known : sortEntry d.name d.mods ∈ envBag env := by
                      rw [← same]
                      exact Multiset.mem_coe.mpr (sortEntry_mem_envRows'.mpr (mem_of_lookupSort found))
                    exact .step (repeatSort_fires d.pure d.strict d.provable d.free d.name
                      (fileTree (ss.map Statement.tree)) (envBag env) known) rest
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
                obtain ⟨unnamed, declaredAll, target⟩ := conditions
                have freshTerm : termName t.name ∉ (([pending (node "file_more" [t.tree,
                    fileTree (ss.map Statement.tree)])] : List Expr) : Multiset Expr) + envBag env := by
                  intro inside
                  rcases mem_one_add.mp inside with same | there
                  · exact absurd (row_inj.mp same).1 (by decide)
                  · exact unnamed (termName_mem_envRows'.mp (Multiset.mem_coe.mp there))
                have first := startTerm_fires t.name (node "tbinders_empty" []) (arrowTree t.args t.ret)
                  (fileTree (ss.map Statement.tree)) (envBag env) freshTerm
                rw [named_bag] at first
                exact .step first (.step (bindersDone_fires t.name (arrowTree t.args t.ret)
                  (fileTree (ss.map Statement.tree)) _)
                  (multiStep_append
                    (arrow_runs env t (fileTree (ss.map Statement.tree)) t.args declaredAll target) rest))
              · cases checked

/-! ## The theorem -/

/-- **A file of sort declarations and term declarations without binders reaches `accepted` exactly when MM0's
rules accept it**, by rewriting of bags with none queries. -/
theorem accepted_reachable_iff (ss : List Statement) :
    (∃ bag : Multiset Expr, (rewritingNone program).MultiStep (start ss) bag ∧ accepted ∈ bag) ↔
      (checkAll empty ss).isSome := by
  constructor
  · rintro ⟨bag, steps, inside⟩
    exact accepted_of_phase (phase_multi steps (phase_start ss)) inside
  · intro checked
    obtain ⟨env, done⟩ := Option.isSome_iff_exists.mp checked
    refine ⟨(([accepted] : List Expr) : Multiset Expr) + envBag env, ?_, mem_one_add.mpr (Or.inl rfl)⟩
    have runs := runs_of_checkAll ss empty env done
    rw [show envBag empty = 0 from rfl, add_zero] at runs
    exact runs

/-- **On the step**: from every state that reads as the bag of such a file, the step reaches a state that reads
as a bag holding `accepted` exactly when MM0's rules accept the file. -/
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

/-- **Accepted on the step**: a state that reads as the file's bag reaches a state that reads as a bag holding
`accepted`. -/
def AcceptedOnTheStep (ss : List Statement) : Prop :=
  ∃ s', (stepSystem ℕ program).MultiStep (listState [pending (fileTree (ss.map Statement.tree))]) s' ∧
    ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag

theorem accepted_on_the_step_iff (ss : List Statement) : AcceptedOnTheStep ss ↔ (checkAll empty ss).isSome :=
  on_the_step ss (start_reads ss)

/-- CeTTa's `term_environment_arrow_positive.mm0`: `strict provable sort wff; term imp: wff > wff > wff;`. -/
def arrowPositive : List Statement :=
  [.sort (sortStmt false true true false "wff"), .term ⟨ident "imp", [ident "wff", ident "wff"], ident "wff"⟩]

/-- CeTTa's `term_environment_constant_positive.mm0`: `sort value; term constant: value;`. -/
def constantPositive : List Statement :=
  [.sort (sortStmt false false false false "value"), .term ⟨ident "constant", [], ident "value"⟩]

/-- CeTTa's `term_environment_pure_target.mm0`: `pure sort set; term constant: set;`. -/
def pureTarget : List Statement :=
  [.sort (sortStmt true false false false "set"), .term ⟨ident "constant", [], ident "set"⟩]

/-- CeTTa's `term_environment_redeclaration.mm0`: `sort value; term constant: value; term constant: value;`. -/
def redeclaration : List Statement :=
  [.sort (sortStmt false false false false "value"), .term ⟨ident "constant", [], ident "value"⟩,
    .term ⟨ident "constant", [], ident "value"⟩]

/-- CeTTa's `term_environment_unknown_sort.mm0`: `term constant: missing;`. -/
def unknownSort : List Statement := [.term ⟨ident "constant", [], ident "missing"⟩]

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

theorem unknownSort_refused : ¬ AcceptedOnTheStep unknownSort := by
  rw [accepted_on_the_step_iff]
  decide +kernel

end Examples

#print axioms Examples.arrowPositive_accepted
#print axioms Examples.constantPositive_accepted
#print axioms Examples.pureTarget_refused
#print axioms Examples.redeclaration_refused
#print axioms Examples.unknownSort_refused
#print axioms phase_step
#print axioms runs_of_checkAll
#print axioms accepted_reachable_iff
#print axioms on_the_step

end Mettapedia.Languages.MM0.OnTheStep.ArrowTermDeclarations
