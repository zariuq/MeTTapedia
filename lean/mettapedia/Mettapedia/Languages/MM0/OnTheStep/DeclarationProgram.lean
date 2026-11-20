import Mettapedia.Languages.MM0.OnTheStep.NoneRewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting

/-!
# MM0's sort and term declarations as a finite program of the step

The step is `RuleSyntax.step` at the one frame over rows with unknowns: a bag store, one match per firing, guards
asked after the firing's own tells, a fixed set of rules beside the store, one store of knowledge. This module
gives a finite program of it that checks the sort and term statements of an `.mm0` file by its own matching.

## Rows

* **Statements are trees of the `.mm0` grammar** of `metta/gslt/module/readers/mm0/MM0Syntax.module`: a node is
  its production's label beside its children (`node`), a leaf its token sort beside its text (`leaf`); labels
  and texts are rows of their code points (`textRow`). The program reads the productions `file_more`,
  `file_empty`, `statement_sort`, `statement_term`, `tbinders_more`, `tbinders_empty`, `tbinder_bound`,
  `tbinder_regular`, `typ_deps`, `ids_more`, `ids_empty`, `bids_more`, `bids_blank`, `bids_empty`,
  `arrow_more`, `arrow_last`, `pure_no` and `strict_no`, with the children in the order of the module's rows.
* **The environment is the store**: one row per declared sort name (`sortName`), one per declared sort with its
  four modifiers (`sortEntry`), one per declared term name (`termName`); while a term is checked, one row per
  binder name of the term (`binderName`) and one per bound variable (`boundVar`), each keyed by the term's
  name, which is fresh, so the rows of one term never meet another's.
* **The cursor** is one row holding the rest of the file (`pending`); a term under check has one working row for
  where its check is (`binders`, `boundNames`, `regularDeps`, `regularNames`, `arrow`, `arrowDeps`,
  `returnDeps`). The file is accepted when the row `accepted` is made.

## The program (`program`, twenty rules)

Each rule takes one row. A lookup in the environment is a read of a row with unknowns, solved by the match; a
freshness condition is a none query whose pattern is written within the unknowns the take binds.

* `declareSort`: the next statement is a sort whose name is no sort's: make its name and entry rows.
  `repeatSort`: the next statement declares a sort again with the same modifiers: accept it, change nothing
  (MM0's GSLT definition, `sort_environment_v1`, and `mm0-rs` accept this; `mm0-c` and the Lean kernel
  `Kernel.TheoryAdmission` refuse every second declaration of a sort, the dialect the program without `repeatSort`
  is meant for, which is not proved here). `acceptFile`: the file is empty: make `accepted`.
* `startTerm`: the next statement is a term whose name is no term's: make its name row and start its binders.
* A bound group `{x y : s}`: `s` is a declared sort that is not `strict`, with no dependencies (`boundGroup`);
  each name is no binder name of the term yet, and becomes a binder name and a bound variable (`boundName`).
* A regular group `(x _ : s d ...)`: `s` is a declared sort (`regularGroup`), each dependency is a bound variable
  of the term declared before (`regularDep`), each named binder is no binder name yet and becomes one
  (`regularName`), a blank binder is skipped (`regularBlank`).
* The arrow type: each argument type is a declared sort whose dependencies are bound variables
  (`arrowArgument`, `arrowDep`); the return type is a declared sort that is not `pure`, with bound dependencies
  (`arrowReturn`, `returnDep`); then the next statement (`returnDepsDone`).

These are the checks of MM0's GSLT definition of term declarations, written by hand after it (`term_environment_v1`: redeclaration,
unknown sort, bound dependencies, strict bound sort, duplicate binder, unknown dependency, pure target), with the
refusals left as stuck runs: a declaration is refused when no rule continues its check.

**In the fragment** (`program_fragment`): every rule has no collect pattern, none queries only, and is range
restricted, so `NoneRewriting.reachable_iff_none` relates the program's rewriting of bags to the step.

**Firing lemmas** (`declareSort_fires` and the rest): each rule rewrites a bag holding its taken row, given its
reads among the other rows and its none patterns missing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.DeclarationProgram

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open NamesOnTheStep (Expr)
open Presentation.Schematic
open Machines (unknowns vars_of_mem_unknowns)
open NoneRewriting

/-! ## Ground rows -/

/-- A list of characters as a row of code points. -/
def codesRow : List Char → Expr
  | [] => .sym 0
  | c :: cs => .app (.sym (c.toNat + 1)) (codesRow cs)

/-- **A text as a row**: its code points, in order. -/
def textRow (s : String) : Expr := codesRow s.toList

/-- A list of rows as a row. -/
def listRow : List Expr → Expr
  | [] => .sym 0
  | e :: es => .app e (listRow es)

/-- **A node of the `.mm0` grammar**: its production's label beside its children. -/
def node (label : String) (kids : List Expr) : Expr := .app (.app (.sym 2) (textRow label)) (listRow kids)

/-- **A leaf of the `.mm0` grammar**: its token sort beside its text. -/
def leaf (sort text : String) : Expr := .app (.app (.sym 1) (textRow sort)) (textRow text)

/-- **A row of the program**: its kind beside its arguments. -/
def row (kind : ℕ) (args : List Expr) : Expr := .app (.app (.sym 3) (.sym kind)) (listRow args)

/-- The rest of the file. -/
def pending (file : Expr) : Expr := row 0 [file]

/-- A declared sort name. -/
def sortName (s : Expr) : Expr := row 1 [s]

/-- A declared sort with its four modifiers. -/
def sortEntry (s modifiers : Expr) : Expr := row 2 [s, modifiers]

/-- A declared term name. -/
def termName (t : Expr) : Expr := row 3 [t]

/-- The file is accepted. -/
def accepted : Expr := row 4 []

/-- The binder groups of term `t` still to check, its arrow type and the rest of the file. -/
def binders (t groups ty rest : Expr) : Expr := row 5 [t, groups, ty, rest]

/-- The names of a bound group of sort `s` still to declare. -/
def boundNames (t names s more ty rest : Expr) : Expr := row 6 [t, names, s, more, ty, rest]

/-- The dependencies of a regular group still to check, then its names. -/
def regularDeps (t deps names more ty rest : Expr) : Expr := row 7 [t, deps, names, more, ty, rest]

/-- The names of a regular group still to declare. -/
def regularNames (t names more ty rest : Expr) : Expr := row 8 [t, names, more, ty, rest]

/-- The arrow type of term `t` still to check. -/
def arrow (t ty rest : Expr) : Expr := row 9 [t, ty, rest]

/-- The dependencies of an argument type still to check, then the rest of the arrow. -/
def arrowDeps (t deps tail rest : Expr) : Expr := row 10 [t, deps, tail, rest]

/-- The dependencies of the return type still to check. -/
def returnDeps (t deps rest : Expr) : Expr := row 11 [t, deps, rest]

/-- A binder name of term `t`. -/
def binderName (t x : Expr) : Expr := row 12 [t, x]

/-- A bound variable of term `t`. -/
def boundVar (t x : Expr) : Expr := row 13 [t, x]

/-- The four modifiers of a sort statement, as one row. -/
def modifiers (p st pr f : Expr) : Expr := listRow [p, st, pr, f]

theorem listRow_injective : ∀ {a b : List Expr}, listRow a = listRow b → a = b
  | [], [], _ => rfl
  | [], _ :: _, same => Expr.noConfusion same
  | _ :: _, [], same => Expr.noConfusion same
  | x :: xs, y :: ys, same => by
      simp only [listRow, Expr.app.injEq] at same
      rw [same.1, listRow_injective same.2]

theorem row_inj {k k' : ℕ} {a a' : List Expr} : row k a = row k' a' ↔ k = k' ∧ a = a' := by
  constructor
  · intro same
    simp only [row, Expr.app.injEq, Expr.sym.injEq, true_and] at same
    exact ⟨same.1, listRow_injective same.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem node_inj {l l' : String} {a a' : List Expr} :
    node l a = node l' a' ↔ textRow l = textRow l' ∧ a = a' := by
  constructor
  · intro same
    simp only [node, Expr.app.injEq, true_and] at same
    exact ⟨same.1, listRow_injective same.2⟩
  · rintro ⟨same, rfl⟩
    simp only [node, same]

/-- The kind of a row of the program; nothing for other rows. -/
def kindOf : Expr → Option ℕ
  | .app (.app (.sym 3) (.sym k)) _ => some k
  | _ => none

@[simp] theorem kindOf_row (k : ℕ) (a : List Expr) : kindOf (row k a) = some k := rfl

/-! ## Patterns -/

/-- Unknown `n` of a rule. -/
def u (n : ℕ) : Tm := .var n

/-- An application pattern. -/
def appP (f a : Tm) : Tm := .app .app (args2 f a)

/-- A list of patterns as a pattern. -/
def listP : List Tm → Tm
  | [] => .const (.sym 0)
  | t :: ts => appP t (listP ts)

/-- A node pattern. -/
def nodeP (label : String) (kids : List Tm) : Tm :=
  appP (appP (.const (.sym 2)) (toTerm (textRow label))) (listP kids)

/-- A row pattern of the program. -/
def rowP (kind : ℕ) (args : List Tm) : Tm := appP (appP (.const (.sym 3)) (.const (.sym kind))) (listP args)

@[simp] theorem inst_u (θ : ℕ → Expr) (n : ℕ) : inst θ (u n) = θ n := rfl

@[simp] theorem inst_appP (θ : ℕ → Expr) (f a : Tm) : inst θ (appP f a) = .app (inst θ f) (inst θ a) := rfl

@[simp] theorem inst_listP (θ : ℕ → Expr) : ∀ ts : List Tm, inst θ (listP ts) = listRow (ts.map (inst θ))
  | [] => rfl
  | t :: ts => by
      show Expr.app (inst θ t) (inst θ (listP ts)) = Expr.app (inst θ t) (listRow (ts.map (inst θ)))
      rw [inst_listP θ ts]

@[simp] theorem inst_nodeP (θ : ℕ → Expr) (label : String) (kids : List Tm) :
    inst θ (nodeP label kids) = node label (kids.map (inst θ)) := by
  show Expr.app (Expr.app (.sym 2) (inst θ (toTerm (textRow label)))) (inst θ (listP kids)) = _
  rw [inst_toTerm, inst_listP]
  rfl

@[simp] theorem inst_rowP (θ : ℕ → Expr) (k : ℕ) (args : List Tm) :
    inst θ (rowP k args) = row k (args.map (inst θ)) := by
  show Expr.app (Expr.app (.sym 3) (.sym k)) (inst θ (listP args)) = _
  rw [inst_listP]
  rfl

/-! ## Rules with takes, reads, none queries and made rows -/

/-- **A rule** with takes, reads, none queries and made rows; no tell, no guard, no collect query. -/
def mkRule (take read missing produce : List Tm) : SRule :=
  ⟨PUnit.unit, ⟨take, read, [], missing.map (Check.predicate .none), produce⟩, []⟩

theorem flatMap_checkTerms_none : ∀ l : List Tm, (l.map (Check.predicate .none)).flatMap checkTerms = l
  | [] => rfl
  | p :: l => by
      rw [List.map_cons, List.flatMap_cons, flatMap_checkTerms_none l]
      rfl

theorem flatMap_nonePatternOf_none : ∀ l : List Tm, (l.map (Check.predicate .none)).flatMap nonePatternOf = l
  | [] => rfl
  | p :: l => by
      rw [List.map_cons, List.flatMap_cons, flatMap_nonePatternOf_none l]
      rfl

theorem flatMap_guardOf_none : ∀ l : List Tm, (l.map (Check.predicate .none)).flatMap guardOf = []
  | [] => rfl
  | p :: l => by
      rw [List.map_cons, List.flatMap_cons, flatMap_guardOf_none l]
      rfl

theorem nonePatternsOf_mkRule (take read missing produce : List Tm) :
    nonePatternsOf (mkRule take read missing produce) = missing :=
  flatMap_nonePatternOf_none missing

theorem equationsOf_mkRule (take read missing produce : List Tm) :
    equationsOf (mkRule take read missing produce) = [] := by
  show [] ++ (missing.map (Check.predicate .none)).flatMap guardOf = []
  rw [flatMap_guardOf_none]
  rfl

theorem written_mkRule (take read missing produce : List Tm) :
    written (mkRule take read missing produce) = missing ++ produce := by
  show [] ++ [] ++ (missing.map (Check.predicate .none)).flatMap checkTerms ++ produce = missing ++ produce
  rw [flatMap_checkTerms_none]
  rfl

/-- **A rule whose none patterns and made rows have only unknowns of its takes and reads is in the fragment.** -/
theorem mkRule_restricted {take read missing produce : List Tm}
    (range : ∀ t ∈ missing ++ produce, ∀ x ∈ unknowns t, ∃ t' ∈ take ++ read, x ∈ unknowns t') :
    NoneRestricted (mkRule take read missing produce) := by
  refine ⟨rfl, List.all_eq_true.mpr fun c inside => ?_, fun t inWritten x vars => ?_⟩
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp inside
    rfl
  · rw [written_mkRule] at inWritten
    obtain ⟨t', inTakes, inUnknowns⟩ := range t inWritten x (Machines.mem_unknowns t vars)
    exact ⟨t', inTakes, vars_of_mem_unknowns t' inUnknowns⟩

/-! ## The program -/

/-- **Declare a sort**: the next statement is a sort whose name is no sort's. -/
def declareSort : SRule :=
  mkRule [rowP 0 [nodeP "file_more" [nodeP "statement_sort" [u 0, u 1, u 2, u 3, u 4], u 5]]] []
    [rowP 1 [u 4]]
    [rowP 1 [u 4], rowP 2 [u 4, listP [u 0, u 1, u 2, u 3]], rowP 0 [u 5]]

/-- **Repeat a sort**: the next statement declares a sort again with the same modifiers. -/
def repeatSort : SRule :=
  mkRule [rowP 0 [nodeP "file_more" [nodeP "statement_sort" [u 0, u 1, u 2, u 3, u 4], u 5]]]
    [rowP 2 [u 4, listP [u 0, u 1, u 2, u 3]]] [] [rowP 0 [u 5]]

/-- **Accept the file**: no statement is left. -/
def acceptFile : SRule := mkRule [rowP 0 [nodeP "file_empty" []]] [] [] [rowP 4 []]

/-- **Start a term**: the next statement is a term whose name is no term's. -/
def startTerm : SRule :=
  mkRule [rowP 0 [nodeP "file_more" [nodeP "statement_term" [u 0, u 1, u 2], u 3]]] [] [rowP 3 [u 0]]
    [rowP 3 [u 0], rowP 5 [u 0, u 1, u 2, u 3]]

/-- **A bound group**: its sort is declared and not `strict`, and its type has no dependencies. -/
def boundGroup : SRule :=
  mkRule [rowP 5 [u 0, nodeP "tbinders_more" [nodeP "tbinder_bound" [u 1, nodeP "typ_deps" [u 2,
      nodeP "ids_empty" []]], u 3], u 4, u 5]]
    [rowP 2 [u 2, listP [u 6, nodeP "strict_no" [], u 7, u 8]]] []
    [rowP 6 [u 0, u 1, u 2, u 3, u 4, u 5]]

/-- **A bound name**: no binder name of the term yet; it becomes a binder name and a bound variable. -/
def boundName : SRule :=
  mkRule [rowP 6 [u 0, nodeP "ids_more" [u 1, u 2], u 3, u 4, u 5, u 6]] [] [rowP 12 [u 0, u 1]]
    [rowP 12 [u 0, u 1], rowP 13 [u 0, u 1], rowP 6 [u 0, u 2, u 3, u 4, u 5, u 6]]

/-- The names of a bound group are declared. -/
def boundNamesDone : SRule :=
  mkRule [rowP 6 [u 0, nodeP "ids_empty" [], u 1, u 2, u 3, u 4]] [] [] [rowP 5 [u 0, u 2, u 3, u 4]]

/-- **A regular group**: its sort is declared; then its dependencies, then its names. -/
def regularGroup : SRule :=
  mkRule [rowP 5 [u 0, nodeP "tbinders_more" [nodeP "tbinder_regular" [u 1, nodeP "typ_deps" [u 2, u 3]], u 4],
      u 5, u 6]]
    [rowP 2 [u 2, u 7]] [] [rowP 7 [u 0, u 3, u 1, u 4, u 5, u 6]]

/-- **A dependency of a regular group** is a bound variable of the term. -/
def regularDep : SRule :=
  mkRule [rowP 7 [u 0, nodeP "ids_more" [u 1, u 2], u 3, u 4, u 5, u 6]] [rowP 13 [u 0, u 1]] []
    [rowP 7 [u 0, u 2, u 3, u 4, u 5, u 6]]

/-- The dependencies of a regular group are checked. -/
def regularDepsDone : SRule :=
  mkRule [rowP 7 [u 0, nodeP "ids_empty" [], u 1, u 2, u 3, u 4]] [] [] [rowP 8 [u 0, u 1, u 2, u 3, u 4]]

/-- **A regular name**: no binder name of the term yet; it becomes one. -/
def regularName : SRule :=
  mkRule [rowP 8 [u 0, nodeP "bids_more" [u 1, u 2], u 3, u 4, u 5]] [] [rowP 12 [u 0, u 1]]
    [rowP 12 [u 0, u 1], rowP 8 [u 0, u 2, u 3, u 4, u 5]]

/-- **A blank binder** is skipped. -/
def regularBlank : SRule :=
  mkRule [rowP 8 [u 0, nodeP "bids_blank" [u 1], u 2, u 3, u 4]] [] [] [rowP 8 [u 0, u 1, u 2, u 3, u 4]]

/-- The names of a regular group are declared. -/
def regularNamesDone : SRule :=
  mkRule [rowP 8 [u 0, nodeP "bids_empty" [], u 1, u 2, u 3]] [] [] [rowP 5 [u 0, u 1, u 2, u 3]]

/-- The binder groups are checked; the arrow type is next. -/
def bindersDone : SRule :=
  mkRule [rowP 5 [u 0, nodeP "tbinders_empty" [], u 1, u 2]] [] [] [rowP 9 [u 0, u 1, u 2]]

/-- **An argument type of the arrow**: its sort is declared; then its dependencies. -/
def arrowArgument : SRule :=
  mkRule [rowP 9 [u 0, nodeP "arrow_more" [nodeP "typ_deps" [u 1, u 2], u 3], u 4]] [rowP 2 [u 1, u 5]] []
    [rowP 10 [u 0, u 2, u 3, u 4]]

/-- **A dependency of an argument type** is a bound variable of the term. -/
def arrowDep : SRule :=
  mkRule [rowP 10 [u 0, nodeP "ids_more" [u 1, u 2], u 3, u 4]] [rowP 13 [u 0, u 1]] []
    [rowP 10 [u 0, u 2, u 3, u 4]]

/-- The dependencies of an argument type are checked. -/
def arrowDepsDone : SRule :=
  mkRule [rowP 10 [u 0, nodeP "ids_empty" [], u 1, u 2]] [] [] [rowP 9 [u 0, u 1, u 2]]

/-- **The return type**: its sort is declared and not `pure`; then its dependencies. -/
def arrowReturn : SRule :=
  mkRule [rowP 9 [u 0, nodeP "arrow_last" [nodeP "typ_deps" [u 1, u 2]], u 3]]
    [rowP 2 [u 1, listP [nodeP "pure_no" [], u 4, u 5, u 6]]] [] [rowP 11 [u 0, u 2, u 3]]

/-- **A dependency of the return type** is a bound variable of the term. -/
def returnDep : SRule :=
  mkRule [rowP 11 [u 0, nodeP "ids_more" [u 1, u 2], u 3]] [rowP 13 [u 0, u 1]] [] [rowP 11 [u 0, u 2, u 3]]

/-- The term is checked; the next statement. -/
def returnDepsDone : SRule := mkRule [rowP 11 [u 0, nodeP "ids_empty" [], u 1]] [] [] [rowP 0 [u 1]]

/-- **The program**: twenty rules, fixed, independent of any file. -/
def program : List SRule :=
  [declareSort, repeatSort, acceptFile, startTerm, boundGroup, boundName, boundNamesDone, regularGroup,
    regularDep, regularDepsDone, regularName, regularBlank, regularNamesDone, bindersDone, arrowArgument,
    arrowDep, arrowDepsDone, arrowReturn, returnDep, returnDepsDone]

/-- **The program is in the fragment**: no collect pattern, none queries only, range restricted. -/
theorem program_fragment : ∀ r ∈ program, NoneRestricted r := by
  intro r member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    exact mkRule_restricted (by decide +kernel)

/-! ## Firing -/

/-- **A rule of the program fires** at a bag holding the instances of its takes beside other rows, when its
reads are among the other rows and its none patterns are missing from the bag. -/
theorem fires {r : SRule} (member : r ∈ program) (θ : ℕ → Expr) (others : Multiset Expr)
    {bag bag' : Multiset Expr}
    (split : ((r.body.take.map (inst θ) : List Expr) : Multiset Expr) + others = bag)
    (readsIn : ∀ q ∈ r.body.read, inst θ q ∈ others) (noEquations : equationsOf r = [])
    (nones : ∀ p ∈ nonePatternsOf r, inst θ p ∉ bag)
    (after : bag' = ((r.body.produce.map (inst θ) : List Expr) : Multiset Expr) + others) :
    RewritesNone program bag bag' :=
  ⟨r, member, θ, others, split, readsIn,
    fun e inside => by rw [noEquations] at inside; exact absurd inside List.not_mem_nil, nones, after⟩

/-- An instantiation listing the values of the unknowns `0, 1, …`. -/
def values (l : List Expr) : ℕ → Expr := fun n => l.getD n (.sym 0)

theorem declareSort_fires (p st pr f s rest : Expr) (others : Multiset Expr)
    (fresh : sortName s ∉
      ([pending (node "file_more" [node "statement_sort" [p, st, pr, f, s], rest])] : Multiset Expr) + others) :
    RewritesNone program
      (([pending (node "file_more" [node "statement_sort" [p, st, pr, f, s], rest])] : Multiset Expr) + others)
      (([sortName s, sortEntry s (modifiers p st pr f), pending rest] : Multiset Expr) + others) :=
  fires (r := declareSort) (by simp [program]) (values [p, st, pr, f, s, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact fresh)
    rfl

theorem repeatSort_fires (p st pr f s rest : Expr) (others : Multiset Expr)
    (known : sortEntry s (modifiers p st pr f) ∈ others) :
    RewritesNone program
      (([pending (node "file_more" [node "statement_sort" [p, st, pr, f, s], rest])] : Multiset Expr) + others)
      (([pending rest] : Multiset Expr) + others) :=
  fires (r := repeatSort) (by simp [program]) (values [p, st, pr, f, s, rest]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact known)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem acceptFile_fires (others : Multiset Expr) :
    RewritesNone program (([pending (node "file_empty" [])] : Multiset Expr) + others)
      (([accepted] : Multiset Expr) + others) :=
  fires (r := acceptFile) (by simp [program]) (values []) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem startTerm_fires (t args ty rest : Expr) (others : Multiset Expr)
    (fresh : termName t ∉
      ([pending (node "file_more" [node "statement_term" [t, args, ty], rest])] : Multiset Expr) + others) :
    RewritesNone program
      (([pending (node "file_more" [node "statement_term" [t, args, ty], rest])] : Multiset Expr) + others)
      (([termName t, binders t args ty rest] : Multiset Expr) + others) :=
  fires (r := startTerm) (by simp [program]) (values [t, args, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact fresh)
    rfl

theorem boundGroup_fires (t names s more ty rest p pr f : Expr) (others : Multiset Expr)
    (known : sortEntry s (modifiers p (node "strict_no" []) pr f) ∈ others) :
    RewritesNone program
      (([binders t (node "tbinders_more" [node "tbinder_bound" [names, node "typ_deps" [s, node "ids_empty" []]],
          more]) ty rest] : Multiset Expr) + others)
      (([boundNames t names s more ty rest] : Multiset Expr) + others) :=
  fires (r := boundGroup) (by simp [program]) (values [t, names, s, more, ty, rest, p, pr, f]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact known)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem boundName_fires (t x xs s more ty rest : Expr) (others : Multiset Expr)
    (fresh : binderName t x ∉
      ([boundNames t (node "ids_more" [x, xs]) s more ty rest] : Multiset Expr) + others) :
    RewritesNone program
      (([boundNames t (node "ids_more" [x, xs]) s more ty rest] : Multiset Expr) + others)
      (([binderName t x, boundVar t x, boundNames t xs s more ty rest] : Multiset Expr) + others) :=
  fires (r := boundName) (by simp [program]) (values [t, x, xs, s, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact fresh)
    rfl

theorem boundNamesDone_fires (t s more ty rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([boundNames t (node "ids_empty" []) s more ty rest] : Multiset Expr) + others)
      (([binders t more ty rest] : Multiset Expr) + others) :=
  fires (r := boundNamesDone) (by simp [program]) (values [t, s, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem regularGroup_fires (t names s deps more ty rest m : Expr) (others : Multiset Expr)
    (known : sortEntry s m ∈ others) :
    RewritesNone program
      (([binders t (node "tbinders_more" [node "tbinder_regular" [names, node "typ_deps" [s, deps]], more]) ty
          rest] : Multiset Expr) + others)
      (([regularDeps t deps names more ty rest] : Multiset Expr) + others) :=
  fires (r := regularGroup) (by simp [program]) (values [t, names, s, deps, more, ty, rest, m]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact known)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem regularDep_fires (t d ds names more ty rest : Expr) (others : Multiset Expr)
    (bound : boundVar t d ∈ others) :
    RewritesNone program
      (([regularDeps t (node "ids_more" [d, ds]) names more ty rest] : Multiset Expr) + others)
      (([regularDeps t ds names more ty rest] : Multiset Expr) + others) :=
  fires (r := regularDep) (by simp [program]) (values [t, d, ds, names, more, ty, rest]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact bound)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem regularDepsDone_fires (t names more ty rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([regularDeps t (node "ids_empty" []) names more ty rest] : Multiset Expr) + others)
      (([regularNames t names more ty rest] : Multiset Expr) + others) :=
  fires (r := regularDepsDone) (by simp [program]) (values [t, names, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem regularName_fires (t x xs more ty rest : Expr) (others : Multiset Expr)
    (fresh : binderName t x ∉ ([regularNames t (node "bids_more" [x, xs]) more ty rest] : Multiset Expr) + others) :
    RewritesNone program
      (([regularNames t (node "bids_more" [x, xs]) more ty rest] : Multiset Expr) + others)
      (([binderName t x, regularNames t xs more ty rest] : Multiset Expr) + others) :=
  fires (r := regularName) (by simp [program]) (values [t, x, xs, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact fresh)
    rfl

theorem regularBlank_fires (t xs more ty rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([regularNames t (node "bids_blank" [xs]) more ty rest] : Multiset Expr) + others)
      (([regularNames t xs more ty rest] : Multiset Expr) + others) :=
  fires (r := regularBlank) (by simp [program]) (values [t, xs, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem regularNamesDone_fires (t more ty rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([regularNames t (node "bids_empty" []) more ty rest] : Multiset Expr) + others)
      (([binders t more ty rest] : Multiset Expr) + others) :=
  fires (r := regularNamesDone) (by simp [program]) (values [t, more, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem bindersDone_fires (t ty rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([binders t (node "tbinders_empty" []) ty rest] : Multiset Expr) + others)
      (([arrow t ty rest] : Multiset Expr) + others) :=
  fires (r := bindersDone) (by simp [program]) (values [t, ty, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem arrowArgument_fires (t s deps tail rest m : Expr) (others : Multiset Expr)
    (known : sortEntry s m ∈ others) :
    RewritesNone program
      (([arrow t (node "arrow_more" [node "typ_deps" [s, deps], tail]) rest] : Multiset Expr) + others)
      (([arrowDeps t deps tail rest] : Multiset Expr) + others) :=
  fires (r := arrowArgument) (by simp [program]) (values [t, s, deps, tail, rest, m]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact known)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem arrowDep_fires (t d ds tail rest : Expr) (others : Multiset Expr) (bound : boundVar t d ∈ others) :
    RewritesNone program
      (([arrowDeps t (node "ids_more" [d, ds]) tail rest] : Multiset Expr) + others)
      (([arrowDeps t ds tail rest] : Multiset Expr) + others) :=
  fires (r := arrowDep) (by simp [program]) (values [t, d, ds, tail, rest]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact bound)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem arrowDepsDone_fires (t tail rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([arrowDeps t (node "ids_empty" []) tail rest] : Multiset Expr) + others)
      (([arrow t tail rest] : Multiset Expr) + others) :=
  fires (r := arrowDepsDone) (by simp [program]) (values [t, tail, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem arrowReturn_fires (t s deps rest st pr f : Expr) (others : Multiset Expr)
    (known : sortEntry s (modifiers (node "pure_no" []) st pr f) ∈ others) :
    RewritesNone program
      (([arrow t (node "arrow_last" [node "typ_deps" [s, deps]]) rest] : Multiset Expr) + others)
      (([returnDeps t deps rest] : Multiset Expr) + others) :=
  fires (r := arrowReturn) (by simp [program]) (values [t, s, deps, rest, st, pr, f]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact known)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem returnDep_fires (t d ds rest : Expr) (others : Multiset Expr) (bound : boundVar t d ∈ others) :
    RewritesNone program
      (([returnDeps t (node "ids_more" [d, ds]) rest] : Multiset Expr) + others)
      (([returnDeps t ds rest] : Multiset Expr) + others) :=
  fires (r := returnDep) (by simp [program]) (values [t, d, ds, rest]) others rfl
    (fun q inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact bound)
    (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

theorem returnDepsDone_fires (t rest : Expr) (others : Multiset Expr) :
    RewritesNone program
      (([returnDeps t (node "ids_empty" []) rest] : Multiset Expr) + others)
      (([pending rest] : Multiset Expr) + others) :=
  fires (r := returnDepsDone) (by simp [program]) (values [t, rest]) others rfl
    (fun q inside => absurd inside List.not_mem_nil) (equationsOf_mkRule _ _ _ _)
    (fun q inside => absurd inside List.not_mem_nil)
    rfl

#print axioms program_fragment
#print axioms declareSort_fires
#print axioms repeatSort_fires
#print axioms acceptFile_fires
#print axioms startTerm_fires
#print axioms boundGroup_fires
#print axioms boundName_fires
#print axioms regularGroup_fires
#print axioms arrowReturn_fires
#print axioms returnDepsDone_fires

end Mettapedia.Languages.MM0.OnTheStep.DeclarationProgram
