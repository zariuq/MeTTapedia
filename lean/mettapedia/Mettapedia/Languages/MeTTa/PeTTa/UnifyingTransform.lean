import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSound

/-!
# PeTTa's calls as firings of a unifying transform step

A **transform rule** takes some values, reads others, and produces new ones.
In the one-way step a pattern `p` gathers a value `t` when `pσ = t`. In the
**unifying step** values may contain the requester's logic variables: a firing
computes one unifier `θ` of all the gathered pairs and applies it to the whole
configuration. Rule variables are fresh at each firing, a stored row is
renamed apart at each use, as Prolog renames clauses, and the requester's
variables are shared by every value they occur in.

A configuration has two parts:

* `rows`, the stored rows of the space. A firing reads a renamed copy of a row
  and never changes or binds the row itself.
* `goals`, the requester's values. A firing takes some of them, and applies its
  unifier to the rest and to what it produces.

Example. With the row `(= (z 0) yes)` and the goals `(demand (z $u) $r)` and
`(pending $u)`, the call rule fires (`call_rule_binds_the_caller`): it takes the
demand, reads the row, unifies `(z $u)` with the renamed head `(z 0)`, and
leaves `(pending 0)` and `(evaluate yes $r)`.

* **Matching is the special case.** On ground goals and ground rows a firing's
  unifier is the matching substitution, and the firing is the one-way firing
  (`unifying_ground_iff_matching`). So results proved for the one-way step hold
  for the firings that bind no shared variable.
* **PeTTa's calls and `match` are firings.** Equations are a read-only rule
  space plus demand. One rule serves every call:
  `take (demand $call $k)`, `read (= $call $body)`, `produce (evaluate $body $k)`
  (`callRule`). One rule serves every `match`:
  `take (query $p $b $k)`, `read $p`, `produce (evaluate $b $k)` (`queryRule`).
  The firings on c6, c5 and a two-sided `match` are computed by the kernel and
  give PeTTa's bindings (`call_rule_binds_the_caller`,
  `call_rule_shares_the_argument`, `query_rule_unifies_two_ways`).
* **`remove-atom` is not one firing.** It removes every row that unifies with
  its argument, and binds nothing: its unifier is a guard that is discarded.
  One unifier cannot remove both `(item 1)` and `(item 2)` with the pattern
  `(item $x)` (`one_unifier_cannot_remove_both`), and PeTTa removes both.
* **The unifier must be most general.** A step that accepts any unifier binds
  the caller's variables arbitrarily: with the head `(z $x)`, the unifier
  `{$u ↦ 7, $x ↦ 7}` of `(z $u)` is not what PeTTa does
  (`any_unifier_overbinds`). The step here uses the unifier `Unifying.unify`
  computes.
* **The list view is unification modulo a theory.** PeTTa's `(cons a b)` pattern
  reads a list by head and tail. As syntax, `(cons $a $b)` and `(1 2)` have no
  unifier (`list_view_is_not_syntactic`); the list view is unification modulo
  `(cons x (y ..)) = (x y ..)`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingTransform

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst isGroundAtom matchAtom)
open Unifying (Unified rename resolve unify ofMatch ofMatch_some GroundRange)

/-! ## Rules, firings and the two steps -/

/-- A transform rule. -/
structure Rule where
  take : List Atom
  read : List Atom
  produce : List Atom

/-- A configuration: the stored rows and the requester's goals. -/
structure Configuration where
  rows : List Atom
  goals : List Atom
  deriving DecidableEq

/-- The rows a firing reads, renamed apart: the `j`-th for the use `use + 1 + j`. -/
def renameRows : Nat → List Atom → List Atom
  | _, [] => []
  | use, row :: rest => rename (use + 1) row :: renameRows (use + 1) rest

/-- Unify the pairs in order, threading the substitution. -/
def unifyPairs : Subst → List (Atom × Atom) → Unified
  | bindings, [] => .ok bindings
  | bindings, (pattern, value) :: rest =>
      (unify bindings pattern value).andThen fun bound => unifyPairs bound rest

/-- Match the pairs in order, threading the substitution. -/
def matchPairs : Subst → List (Atom × Atom) → Option Subst
  | bindings, [] => some bindings
  | bindings, (pattern, value) :: rest =>
      (matchAtom bindings pattern value).bind fun bound => matchPairs bound rest

/-- The gathered pairs of a firing: each take pattern, renamed for `use`, with
its goal; each read pattern with its row, renamed apart. -/
def gathered (rule : Rule) (use : Nat) (taken readRows : List Atom) : List (Atom × Atom) :=
  (rule.take.map (rename use)).zip taken ++ (rule.read.map (rename use)).zip (renameRows use readRows)

/-- **The unifying step.** For some use number, goals taken (one per take
pattern) and rows read (one per read pattern), the gathered pairs have the
unifier `θ`; the goals not taken and the produced goals are instantiated by `θ`. -/
def UnifyingStep (rule : Rule) (source target : Configuration) : Prop :=
  ∃ (use : Nat) (θ : Subst) (taken rest readRows : List Atom),
    source.goals.Perm (taken ++ rest) ∧ (∀ row ∈ readRows, row ∈ source.rows) ∧
    taken.length = rule.take.length ∧ readRows.length = rule.read.length ∧
    unifyPairs [] (gathered rule use taken readRows) = .ok θ ∧
    target = { rows := source.rows,
               goals := (rest ++ rule.produce.map (rename use)).map (resolve θ) }

/-- **The one-way step.** The gathered pairs are matched: `σ` instantiates the
patterns to the gathered values. The goals not taken stay as they are; the
produced goals are the instances. -/
def MatchingStep (rule : Rule) (source target : Configuration) : Prop :=
  ∃ (use : Nat) (σ : Subst) (taken rest readRows : List Atom),
    source.goals.Perm (taken ++ rest) ∧ (∀ row ∈ readRows, row ∈ source.rows) ∧
    taken.length = rule.take.length ∧ readRows.length = rule.read.length ∧
    matchPairs [] (gathered rule use taken readRows) = some σ ∧
    target = { rows := source.rows,
               goals := rest ++ (rule.produce.map (rename use)).map (applySubst σ) }

/-! ## Matching is the special case -/

theorem renameRows_ground : ∀ (use : Nat) (rows : List Atom),
    (∀ row ∈ rows, isGroundAtom row = true) → renameRows use rows = rows
  | _, [], _ => rfl
  | use, row :: rest, ground => by
      simp only [renameRows, Unifying.rename_ground _ row (ground row List.mem_cons_self),
        renameRows_ground (use + 1) rest (fun item member => ground item (List.mem_cons_of_mem _ member))]

theorem mem_of_mem_zip_right {pairs : List (Atom × Atom)} {first second : List Atom}
    (zipped : pairs = first.zip second) {pair : Atom × Atom} (member : pair ∈ pairs) :
    pair.2 ∈ second := by
  subst zipped
  exact (List.of_mem_zip member).2

/-- On pairs whose values are ground, unifying the pairs is matching them. -/
theorem unifyPairs_ground : ∀ (pairs : List (Atom × Atom)) (bindings : Subst),
    GroundRange bindings → (∀ pair ∈ pairs, isGroundAtom pair.2 = true) →
      unifyPairs bindings pairs = ofMatch (matchPairs bindings pairs)
  | [], _, _, _ => rfl
  | (pattern, value) :: rest, bindings, range, ground => by
      have here := ground (pattern, value) List.mem_cons_self
      simp only [unifyPairs, matchPairs, Unifying.unify_ground range here]
      cases matched : matchAtom bindings pattern value with
      | none => rfl
      | some bound =>
          simp only [ofMatch_some, Unified.ok_andThen, Option.bind_some]
          exact unifyPairs_ground rest bound (Unifying.matchAtom_groundRange range here matched)
            (fun pair member => ground pair (List.mem_cons_of_mem _ member))

/-- **Matching is the special case of the unifying step**: on ground goals and
ground rows, a configuration has a unifying step to `target` exactly when it has
a one-way step to `target`. -/
theorem unifying_ground_iff_matching {rule : Rule} {source target : Configuration}
    (groundGoals : ∀ goal ∈ source.goals, isGroundAtom goal = true)
    (groundRows : ∀ row ∈ source.rows, isGroundAtom row = true) :
    UnifyingStep rule source target ↔ MatchingStep rule source target := by
  have pairsGround : ∀ (use : Nat) (taken rest readRows : List Atom),
      source.goals.Perm (taken ++ rest) → (∀ row ∈ readRows, row ∈ source.rows) →
      ∀ pair ∈ gathered rule use taken readRows, isGroundAtom pair.2 = true := by
    intro use taken rest readRows perm rows pair member
    rcases List.mem_append.mp member with member | member
    · exact groundGoals _ (perm.symm.subset (List.mem_append_left _
        (mem_of_mem_zip_right rfl member)))
    · have inRenamed := mem_of_mem_zip_right rfl member
      rw [renameRows_ground use readRows (fun row inRead => groundRows row (rows row inRead))]
        at inRenamed
      exact groundRows _ (rows _ inRenamed)
  have restFixed : ∀ (θ : Subst) (taken rest : List Atom), source.goals.Perm (taken ++ rest) →
      rest.map (resolve θ) = rest := by
    intro θ taken rest perm
    conv_rhs => rw [← List.map_id rest]
    apply List.map_congr_left
    intro goal member
    exact Unifying.applySubst_ground θ goal
      (groundGoals goal (perm.symm.subset (List.mem_append_right _ member)))
  constructor
  · rintro ⟨use, θ, taken, rest, readRows, perm, rows, takeLength, readLength, unified, result⟩
    rw [unifyPairs_ground _ [] (fun _ never => by cases never)
      (pairsGround use taken rest readRows perm rows)] at unified
    cases matched : matchPairs [] (gathered rule use taken readRows) with
    | none => rw [matched] at unified; cases unified
    | some σ =>
        rw [matched] at unified
        cases unified
        refine ⟨use, θ, taken, rest, readRows, perm, rows, takeLength, readLength, matched, ?_⟩
        rw [result, List.map_append, restFixed θ taken rest perm]
  · rintro ⟨use, σ, taken, rest, readRows, perm, rows, takeLength, readLength, matched, result⟩
    refine ⟨use, σ, taken, rest, readRows, perm, rows, takeLength, readLength, ?_, ?_⟩
    · rw [unifyPairs_ground _ [] (fun _ never => by cases never)
        (pairsGround use taken rest readRows perm rows), matched]
      rfl
    · rw [result, List.map_append, restFixed σ taken rest perm]

/-! ## PeTTa's calls and `match` as rules -/

private def sym (name : String) : Atom := .symbol name
private def var (name : String) : Atom := .var name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-- **The call rule**: equations are read-only rows, a call is a demand. -/
def callRule : Rule where
  take := [call "demand" [var "call", var "k"]]
  read := [call "=" [var "call", var "body"]]
  produce := [call "evaluate" [var "body", var "k"]]

/-- **The `match` rule**: a query takes its demand and reads one row that
unifies with its pattern. -/
def queryRule : Rule where
  take := [call "query" [var "p", var "b", var "k"]]
  read := [var "p"]
  produce := [call "evaluate" [var "b", var "k"]]

/-- The configurations one step of `rule` reaches by taking the first goal and
reading the given row, at the use number `use`. -/
def fireOn (rule : Rule) (use : Nat) (source : Configuration) (taken : List Atom)
    (rest : List Atom) (readRows : List Atom) : Option Configuration :=
  match unifyPairs [] (gathered rule use taken readRows) with
  | .ok θ => some { rows := source.rows,
                    goals := (rest ++ rule.produce.map (rename use)).map (resolve θ) }
  | _ => none

theorem step_of_fireOn {rule : Rule} {use : Nat} {source target : Configuration}
    {taken rest readRows : List Atom} (perm : source.goals.Perm (taken ++ rest))
    (rows : ∀ row ∈ readRows, row ∈ source.rows) (takeLength : taken.length = rule.take.length)
    (readLength : readRows.length = rule.read.length)
    (fired : fireOn rule use source taken rest readRows = some target) :
    UnifyingStep rule source target := by
  unfold fireOn at fired
  cases unified : unifyPairs [] (gathered rule use taken readRows) with
  | ok θ =>
      rw [unified] at fired
      cases fired
      exact ⟨use, θ, taken, rest, readRows, perm, rows, takeLength, readLength, unified, rfl⟩
  | clash => rw [unified] at fired; cases fired
  | exhausted => rw [unified] at fired; cases fired

/-- c6 as a firing: the call rule takes `(demand (z $u) $r)`, reads the row
`(= (z 0) yes)`, and binds the caller's `$u` in every goal: `(pending $u)`
becomes `(pending 0)`. -/
theorem call_rule_binds_the_caller :
    fireOn callRule 0
        { rows := [call "=" [call "z" [.grounded (.int 0)], sym "yes"]],
          goals := [call "demand" [call "z" [var "u"], var "r"], call "pending" [var "u"]] }
        [call "demand" [call "z" [var "u"], var "r"]] [call "pending" [var "u"]]
        [call "=" [call "z" [.grounded (.int 0)], sym "yes"]] =
      some { rows := [call "=" [call "z" [.grounded (.int 0)], sym "yes"]],
             goals := [call "pending" [.grounded (.int 0)], call "evaluate" [sym "yes", var "r"]] } := by
  decide +kernel

/-- c5 as a firing: the row `(= (g $x) (let $x 5 $x))`, renamed apart, unifies
its `$x` with the caller's `$u`, so the caller's `(pending $u)` and the body it
produces share one variable: `(pending $x#1)` and `(let $x#1 5 $x#1)`. -/
theorem call_rule_shares_the_argument :
    fireOn callRule 0
        { rows := [call "=" [call "g" [var "x"], call "let" [var "x", .grounded (.int 5), var "x"]]],
          goals := [call "demand" [call "g" [var "u"], var "r"], call "pending" [var "u"]] }
        [call "demand" [call "g" [var "u"], var "r"]] [call "pending" [var "u"]]
        [call "=" [call "g" [var "x"], call "let" [var "x", .grounded (.int 5), var "x"]]] =
      some { rows := [call "=" [call "g" [var "x"], call "let" [var "x", .grounded (.int 5), var "x"]]],
             goals := [call "pending" [var "x#1"],
               call "evaluate" [call "let" [var "x#1", .grounded (.int 5), var "x#1"], var "r"]] } := by
  decide +kernel

/-- u3 as a firing: the query `(fact 1 $v)` reads the stored row `(fact $y 2)`,
renamed apart, and binds `$v` to `2`. -/
theorem query_rule_unifies_two_ways :
    fireOn queryRule 0
        { rows := [call "fact" [var "y", .grounded (.int 2)]],
          goals := [call "query" [call "fact" [.grounded (.int 1), var "v"], var "v", var "r"]] }
        [call "query" [call "fact" [.grounded (.int 1), var "v"], var "v", var "r"]] []
        [call "fact" [var "y", .grounded (.int 2)]] =
      some { rows := [call "fact" [var "y", .grounded (.int 2)]],
             goals := [call "evaluate" [.grounded (.int 2), var "r"]] } := by
  decide +kernel

/-- No firing binds a row's own variables: reading `(fact $y 2)` twice gives
two separate copies (here the second read is of the same row, at the next use). -/
theorem rows_are_renamed_apart :
    renameRows 0 [call "fact" [var "y", .grounded (.int 2)], call "fact" [var "y", .grounded (.int 2)]] =
      [call "fact" [var "y#1", .grounded (.int 2)], call "fact" [var "y#2", .grounded (.int 2)]] := by
  decide +kernel

/-! ## Each equation is a rule of a read-only rule space -/

/-- The rule of one equation `(= (f p ..) b)`: it takes the demand `(demand (f p ..))`
and produces `(evaluate b)`. The rule is never taken, so the space of
equations is read-only; renaming at each firing makes its variables fresh. -/
def equationRule (equation : SpaceSemantics.Equation) : Rule where
  take := [call "demand" [.expression (.symbol equation.head :: equation.arguments)]]
  read := []
  produce := [call "evaluate" [equation.body]]

/-- A pattern without PeTTa's list view anywhere in it. -/
def noListView : Atom → Bool
  | .expression items => !Unifying.consView items && listNoView items
  | _ => true
where
  listNoView : List Atom → Bool
    | [] => true
    | first :: rest => noListView first && listNoView rest

theorem noListView_items {items : List Atom} (clear : noListView (.expression items) = true) :
    Unifying.consView items = false ∧ ∀ item ∈ items, noListView item = true := by
  have listAll : ∀ items : List Atom, noListView.listNoView items = true →
      ∀ item ∈ items, noListView item = true := by
    intro items
    induction items with
    | nil => intro _ item member; cases member
    | cons first rest ih =>
        intro clearList item member
        simp only [noListView.listNoView, Bool.and_eq_true] at clearList
        rcases List.mem_cons.mp member with same | member
        · subst same; exact clearList.1
        · exact ih clearList.2 item member
  simp only [noListView, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at clear
  exact ⟨clear.1, listAll items clear.2⟩

/-- Without the list view, `matchValue` is `matchAtom`. -/
theorem matchValue_eq_matchAtom : ∀ (size : Nat) (bindings : Subst) (pattern value : Atom),
    Unifying.atomSize pattern ≤ size → noListView pattern = true →
      SpaceSemantics.matchValue bindings pattern value = matchAtom bindings pattern value := by
  intro size
  induction size with
  | zero => intro _ pattern _ small; have := Unifying.atomSize_pos pattern; omega
  | succ size ih =>
      intro bindings pattern value small clear
      cases pattern with
      | var _ => exact Unifying.matchValue_atom bindings _ value rfl
      | symbol _ => exact Unifying.matchValue_atom bindings _ value rfl
      | grounded _ => exact Unifying.matchValue_atom bindings _ value rfl
      | expression patterns =>
          obtain ⟨notView, clearItems⟩ := noListView_items clear
          cases value with
          | expression values =>
              rw [SpaceSemantics.matchValue_expression_of_not_cons bindings patterns values
                (Unifying.not_cons_of_consView notView)]
              simp only [matchAtom]
              have lists : ∀ (patterns values : List Atom) (current : Subst),
                  (∀ item ∈ patterns, Unifying.atomSize item ≤ size) →
                  (∀ item ∈ patterns, noListView item = true) →
                  SpaceSemantics.matchValue.matchValues current patterns values =
                    matchAtom.matchAtomList current patterns values := by
                intro patterns
                induction patterns with
                | nil =>
                    intro values _ _ _
                    cases values <;> simp [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
                | cons first rest restIh =>
                    intro values current smallItems clearList
                    cases values with
                    | nil => simp [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
                    | cons value remaining =>
                        simp only [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
                        rw [ih current first value (smallItems first List.mem_cons_self)
                          (clearList first List.mem_cons_self)]
                        cases matchAtom current first value with
                        | none => rfl
                        | some middle =>
                            simp only [Option.bind_eq_bind, Option.bind_some]
                            exact restIh remaining middle
                              (fun item member => smallItems item (List.mem_cons_of_mem _ member))
                              (fun item member => clearList item (List.mem_cons_of_mem _ member))
              exact lists patterns values bindings
                (fun item member => by
                  have := Unifying.atomSize_lt_of_mem member
                  omega) clearItems
          | var _ => rw [Unifying.matchValue_expression_constant bindings patterns _ rfl]; rfl
          | symbol _ => rw [Unifying.matchValue_expression_constant bindings patterns _ rfl]; rfl
          | grounded _ => rw [Unifying.matchValue_expression_constant bindings patterns _ rfl]; rfl

theorem consView_iff (items : List Atom) :
    Unifying.consView items = true ↔ ∃ first rest, items = [.symbol "cons", first, rest] :=
  ⟨Unifying.consView_true, by rintro ⟨first, rest, rfl⟩; rfl⟩

theorem renameList_eq_map (use : Nat) : ∀ items : List Atom,
    rename.renameList use items = items.map (rename use)
  | [] => rfl
  | first :: rest => by simp [rename.renameList, renameList_eq_map use rest]

theorem rename_eq_symbol {use : Nat} {term : Atom} {name : String}
    (same : rename use term = .symbol name) : term = .symbol name := by
  cases term <;> simp_all [rename]

/-- Renaming keeps the list view where it was, and only there. -/
theorem consView_renameList (use : Nat) (items : List Atom) :
    Unifying.consView (rename.renameList use items) = Unifying.consView items := by
  rw [Bool.eq_iff_iff, consView_iff, consView_iff]
  constructor
  · rintro ⟨first, rest, same⟩
    rcases items with _ | ⟨one, _ | ⟨two, _ | ⟨three, _ | ⟨four, more⟩⟩⟩⟩
    all_goals simp only [rename.renameList, List.cons.injEq, reduceCtorEq, and_false,
      List.ne_cons_self] at same
    obtain ⟨head, -, -⟩ := same
    exact ⟨two, three, by rw [rename_eq_symbol head]⟩
  · rintro ⟨first, rest, rfl⟩
    exact ⟨rename use first, rename use rest, rfl⟩

theorem noListView_rename (use : Nat) : ∀ pattern : Atom,
    noListView pattern = true → noListView (rename use pattern) = true
  | .var _, _ => rfl
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, clear => by
      obtain ⟨notView, clearItems⟩ := noListView_items clear
      simp only [noListView, Bool.and_eq_true] at clear
      simp only [rename, noListView, Bool.and_eq_true, consView_renameList, notView,
        Bool.not_false, true_and]
      exact list items clear.2
where
  list : ∀ items : List Atom, noListView.listNoView items = true →
      noListView.listNoView (rename.renameList use items) = true
    | [], _ => rfl
    | first :: rest, clear => by
        simp only [noListView.listNoView, Bool.and_eq_true] at clear
        simp only [rename.renameList, noListView.listNoView, Bool.and_eq_true]
        exact ⟨noListView_rename use first clear.1, list rest clear.2⟩

/-- **A call is a firing of its equation's rule.** With ground arguments and
argument patterns without the list view, the PeTTa machine selects the
equation (`Unifying.unifyArguments`, as `Unifying.selections` does) with the
substitution `θ` exactly when the equation's rule, renamed for the same use,
fires on the demand `(demand (f v ..))` with the same `θ`. -/
theorem call_is_equation_firing (equation : SpaceSemantics.Equation) (values : List Atom)
    (use : Nat) (θ : Subst)
    (ground : ∀ value ∈ values, isGroundAtom value = true)
    (clear : ∀ pattern ∈ equation.arguments, noListView pattern = true) :
    Unifying.unifyArguments [] (equation.arguments.map (rename use)) values = .ok θ ↔
      unifyPairs [] (gathered (equationRule equation) use
        [call "demand" [.expression (.symbol equation.head :: values)]] []) = .ok θ := by
  have groundCall : isGroundAtom (call "demand" [.expression (.symbol equation.head :: values)]) = true := by
    have list : ∀ values : List Atom, (∀ value ∈ values, isGroundAtom value = true) →
        isGroundAtom.isGroundList values = true := by
      intro values
      induction values with
      | nil => intro _; rfl
      | cons first rest ih =>
          intro groundAll
          simp only [isGroundAtom.isGroundList, Bool.and_eq_true]
          exact ⟨groundAll first List.mem_cons_self,
            ih (fun item member => groundAll item (List.mem_cons_of_mem _ member))⟩
    simp [call, isGroundAtom, isGroundAtom.isGroundList, list values ground]
  have renamedClear : ∀ pattern ∈ equation.arguments.map (rename use), noListView pattern = true := by
    intro pattern member
    obtain ⟨original, inArguments, rfl⟩ := List.mem_map.mp member
    exact noListView_rename use original (clear original inArguments)
  have lists : ∀ (patterns values : List Atom) (current : Subst),
      (∀ pattern ∈ patterns, noListView pattern = true) →
      SpaceSemantics.matchValue.matchValues current patterns values =
        matchAtom.matchAtomList current patterns values := by
    intro patterns
    induction patterns with
    | nil => intro values _ _; cases values <;> simp [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
    | cons first rest ih =>
        intro values current clearAll
        cases values with
        | nil => simp [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
        | cons value remaining =>
            simp only [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
            rw [matchValue_eq_matchAtom (Unifying.atomSize first) current first value le_rfl
              (clearAll first List.mem_cons_self)]
            cases matchAtom current first value with
            | none => rfl
            | some middle =>
                simp only [Option.bind_eq_bind, Option.bind_some]
                exact ih remaining middle (fun item member => clearAll item (List.mem_cons_of_mem _ member))
  rw [Unifying.arguments_ground (fun _ never => by cases never) ground,
    lists _ values [] renamedClear]
  simp only [gathered, equationRule, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, List.append_nil, renameRows, unifyPairs]
  rw [Unifying.unify_ground (bindings := []) (fun _ never => by cases never) groundCall]
  simp only [call, rename, renameList_eq_map, List.map_cons, matchAtom, matchAtom.matchAtomList,
    beq_self_eq_true, ↓reduceIte]
  cases matchAtom.matchAtomList [] (equation.arguments.map (rename use)) values <;>
    simp [matchAtom.matchAtomList]

/-! ## What does not fit -/

/-- **`remove-atom` is not one firing.** One unifier cannot unify the pattern
`(item $x)` with both `(item 1)` and `(item 2)`, while PeTTa's `remove-atom`
removes both rows (`Unifying.Controls.removal_by_unification`): its unifier is
a guard, tested row by row and discarded. -/
theorem one_unifier_cannot_remove_both :
    ¬ ∃ θ : Subst,
      applySubst θ (call "item" [var "x"]) = applySubst θ (call "item" [.grounded (.int 1)]) ∧
      applySubst θ (call "item" [var "x"]) = applySubst θ (call "item" [.grounded (.int 2)]) := by
  rintro ⟨θ, one, two⟩
  have both := one.symm.trans two
  simp [call, applySubst, applySubst.applySubstList] at both

/-- **The unifier must be most general.** With the head `(z $x)`, the
substitution `{$u ↦ 7, $x ↦ 7}` unifies `(z $u)` with `(z $x)`, and binds the
caller's `$u`, which PeTTa never does for this head; the computed unifier binds
only the head's variable. -/
theorem any_unifier_overbinds :
    applySubst [("u", .grounded (.int 7)), ("x", .grounded (.int 7))] (call "z" [var "u"]) =
        applySubst [("u", .grounded (.int 7)), ("x", .grounded (.int 7))] (call "z" [var "x"]) ∧
      unify [] (call "z" [var "x"]) (call "z" [var "u"]) = .ok [("x", var "u")] := by
  constructor
  · rfl
  · decide +kernel

/-- **The list view is not syntactic unification.** `(cons $a $b)` and `(1 2)`
have no syntactic unifier, while the list view reads `(1 2)` as head `1` and
tail `(2)`. -/
theorem list_view_is_not_syntactic :
    unify [] (call "cons" [var "a", var "b"]) (.expression [.grounded (.int 1), .grounded (.int 2)]) =
        .clash ∧
      Unifying.unifyAsPattern [] (call "cons" [var "a", var "b"])
        (.expression [.grounded (.int 1), .grounded (.int 2)]) =
        .ok [("b", .expression [.grounded (.int 2)]), ("a", .grounded (.int 1))] := by
  decide +kernel

/-! ## Where no shared variable is bound -/

/-- **The one-way step, relationally** (the calculus's `Matches`/`Reads`): some
`σ` instantiates each renamed take pattern to its goal and each renamed read
pattern to its row, renamed apart as the unifying step reads it; the goals not
taken stay, and the produced goals are the instances. -/
def OneWayStep (rule : Rule) (source target : Configuration) : Prop :=
  ∃ (use : Nat) (σ : Subst) (taken rest readRows : List Atom),
    source.goals.Perm (taken ++ rest) ∧ (∀ row ∈ readRows, row ∈ source.rows) ∧
    taken.length = rule.take.length ∧ readRows.length = rule.read.length ∧
    (∀ pair ∈ gathered rule use taken readRows, applySubst σ pair.1 = pair.2) ∧
    target = { rows := source.rows,
               goals := rest ++ (rule.produce.map (rename use)).map (applySubst σ) }

/-- Unifying the pairs in order is sound: the result makes every pair equal. -/
theorem unifyPairs_sound : ∀ (pairs : List (Atom × Atom)) (bindings bound : Subst),
    Unifying.Idempotent bindings → unifyPairs bindings pairs = .ok bound →
      Unifying.Idempotent bound ∧ Unifying.Refines bindings bound ∧
        ∀ pair ∈ pairs, resolve bound pair.1 = resolve bound pair.2
  | [], bindings, bound, idempotent, unified => by
      simp only [unifyPairs, Unified.ok.injEq] at unified
      subst unified
      exact ⟨idempotent, Unifying.Refines.refl idempotent, fun _ never => by cases never⟩
  | (pattern, value) :: rest, bindings, bound, idempotent, unified => by
      simp only [unifyPairs] at unified
      cases step : unify bindings pattern value with
      | clash => rw [step] at unified; cases unified
      | exhausted => rw [step] at unified; cases unified
      | ok middle =>
          rw [step, Unified.ok_andThen] at unified
          obtain ⟨middleIdempotent, middleRefines, middleEqual⟩ :=
            Unifying.unifyTerms_sound _ bindings middle pattern value idempotent step
          obtain ⟨boundIdempotent, boundRefines, restEqual⟩ :=
            unifyPairs_sound rest middle bound middleIdempotent unified
          refine ⟨boundIdempotent, middleRefines.trans boundRefines, ?_⟩
          intro pair member
          rcases List.mem_cons.mp member with same | member
          · subst same
            rw [← boundRefines pattern, ← boundRefines value, middleEqual]
          · exact restEqual pair member

theorem idempotent_nil : Unifying.Idempotent [] := by
  intro _ _ found
  cases found

/-- **Matching is the special case of the unifying step, where no shared
variable is bound**: a unifying firing whose unifier fixes every goal and every
renamed row it reads (binds none of their variables) is a one-way firing, with
`σ = θ`. So every property of all one-way firings holds for these unifying
firings. -/
theorem oneWay_of_unifying_fixed {rule : Rule} {source target : Configuration}
    (use : Nat) (θ : Subst) (taken rest readRows : List Atom)
    (perm : source.goals.Perm (taken ++ rest))
    (rows : ∀ row ∈ readRows, row ∈ source.rows)
    (takeLength : taken.length = rule.take.length) (readLength : readRows.length = rule.read.length)
    (unified : unifyPairs [] (gathered rule use taken readRows) = .ok θ)
    (result : target = { rows := source.rows,
                         goals := (rest ++ rule.produce.map (rename use)).map (resolve θ) })
    (fixesGoals : ∀ goal ∈ source.goals, resolve θ goal = goal)
    (fixesRows : ∀ copy ∈ renameRows use readRows, resolve θ copy = copy) :
    OneWayStep rule source target := by
  obtain ⟨_, _, equal⟩ := unifyPairs_sound _ [] θ idempotent_nil unified
  refine ⟨use, θ, taken, rest, readRows, perm, rows, takeLength, readLength, ?_, ?_⟩
  · intro pair member
    have same := equal pair member
    rcases List.mem_append.mp member with inTake | inRead
    · rw [show applySubst θ pair.1 = resolve θ pair.1 from rfl, same]
      exact fixesGoals _ (perm.symm.subset (List.mem_append_left _ (mem_of_mem_zip_right rfl inTake)))
    · rw [show applySubst θ pair.1 = resolve θ pair.1 from rfl, same]
      exact fixesRows _ (mem_of_mem_zip_right rfl inRead)
  · rw [result, List.map_append]
    congr 2
    conv_rhs => rw [← List.map_id rest]
    apply List.map_congr_left
    intro goal member
    exact fixesGoals goal (perm.symm.subset (List.mem_append_right _ member))

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingTransform
