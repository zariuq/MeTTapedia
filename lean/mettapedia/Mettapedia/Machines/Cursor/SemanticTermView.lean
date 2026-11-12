import Mathlib.Tactic

/-!
# Logical observations of cells and flat blocks

Physical cells and flat blocks expose one sequence view. A block may end in
an open tail or an improper value; there is no bounded prefix in this model.
Expression endings and list-value endings remain different semantic labels.
Representation equivalence therefore does not erase a value-kind distinction.

The reference constructs a semantic term. The operational observer instead
walks a small cursor, exposing a head and residual without constructing the
whole term. These independent computations agree at every finite path.

This is a finite, free-constructor profile. Quotations, mutable identities,
numeric conversion, rational terms and matching modulo program equations need
their own observation interpretations. No such feature is forbidden by the
interface or silently treated as a rigid structural clash here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SemanticTermView

inductive EndKind where
  | expression
  | listValue
  deriving DecidableEq, Repr

inductive Label where
  | symbol (name : Nat)
  | ending (kind : EndKind)
  | opaque (kind identity : Nat)
  deriving DecidableEq, Repr

inductive Term where
  | rigid (label : Label)
  | var (name : Nat)
  | pair (first rest : Term)
  deriving DecidableEq, Repr

inductive Stored where
  | rigid (label : Label)
  | var (name : Nat)
  | cell (first rest : Stored)
  | block (items : List Stored) (rest : Stored)
  deriving Repr

def Stored.denote (value : Stored) : Term :=
  match value with
  | .rigid label => .rigid label
  | .var name => .var name
  | .cell first rest => .pair first.denote rest.denote
  | .block items rest =>
      (items.attach.map fun item => item.val.denote).foldr Term.pair rest.denote
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have smaller := List.sizeOf_lt_of_mem item.property
    omega

theorem denote_block (items : List Stored) (rest : Stored) :
    (Stored.block items rest).denote = (items.map Stored.denote).foldr Term.pair rest.denote := by
  rw [Stored.denote]
  simp

inductive Focus where
  | value (stored : Stored)
  | segment (items : List Stored) (rest : Stored)

def Focus.denote : Focus → Term
  | .value stored => stored.denote
  | .segment items rest => (items.map Stored.denote).foldr Term.pair rest.denote

inductive View where
  | rigid (label : Label)
  | var (name : Nat)
  | pair (first rest : Focus)

def View.denote : View → Term
  | .rigid label => .rigid label
  | .var name => .var name
  | .pair first rest => .pair first.denote rest.denote

def read (cursor : Focus) : View :=
  match cursor with
  | .value (.rigid label) => .rigid label
  | .value (.var name) => .var name
  | .value (.cell first rest) => .pair (.value first) (.value rest)
  | .value (.block items rest) => read (.segment items rest)
  | .segment [] rest => read (.value rest)
  | .segment (first :: later) rest => .pair (.value first) (.segment later rest)
termination_by sizeOf cursor
decreasing_by all_goals simp_wf

/-- The cursor interprets the stored value without requiring its complete
semantic tree as operational input. -/
theorem read_correct (cursor : Focus) : (read cursor).denote = cursor.denote := by
  fun_induction read cursor <;>
    simp_all [View.denote, Focus.denote, Stored.denote, denote_block]

inductive Direction where
  | first
  | rest
  deriving DecidableEq, Repr

abbrev Path := List Direction

inductive Observation where
  | unknown
  | absent
  | rigid (label : Label)
  | pair
  deriving DecidableEq, Repr

def project : Term → Path → Observation
  | .var _, _ => .unknown
  | .rigid label, [] => .rigid label
  | .pair _ _, [] => .pair
  | .rigid _, _ :: _ => .absent
  | .pair first _, .first :: more => project first more
  | .pair _ rest, .rest :: more => project rest more

def observe (cursor : Focus) (path : Path) : Observation :=
  match read cursor, path with
  | .var _, _ => .unknown
  | .rigid label, [] => .rigid label
  | .pair _ _, [] => .pair
  | .rigid _, _ :: _ => .absent
  | .pair first _, .first :: more => observe first more
  | .pair _ rest, .rest :: more => observe rest more
termination_by path.length

theorem observe_correct (cursor : Focus) (path : Path) :
    observe cursor path = project cursor.denote path := by
  induction path generalizing cursor with
  | nil =>
      rw [observe.eq_def, ← read_correct cursor]
      cases read cursor <;> rfl
  | cons direction more ih =>
      rw [observe.eq_def, ← read_correct cursor]
      cases read cursor <;> cases direction
      all_goals first | rfl | exact ih _

theorem representation_invariant (first second : Focus) (same : first.denote = second.denote)
    (path : Path) : observe first path = observe second path := by
  rw [observe_correct, observe_correct, same]

def substitute (environment : Nat → Term) : Term → Term
  | .rigid label => .rigid label
  | .var name => environment name
  | .pair first rest => .pair (substitute environment first) (substitute environment rest)

def Unifies (query row : Term) : Prop :=
  ∃ queryEnvironment rowEnvironment,
    substitute queryEnvironment query = substitute rowEnvironment row

theorem known_projection_stable (environment : Nat → Term) (term : Term) (path : Path)
    (known : project term path ≠ .unknown) :
    project (substitute environment term) path = project term path := by
  induction path generalizing term with
  | nil => cases term <;> simp_all [project, substitute]
  | cons direction more ih =>
      cases term with
      | rigid label => rfl
      | var name => simp [project] at known
      | pair first rest =>
          cases direction <;> simp_all [project, substitute]

def compatible : Observation → Observation → Bool
  | .unknown, _ | _, .unknown => true
  | first, second => decide (first = second)

/-- Different rigid observations refute unification; an unresolved variable
or tail never licenses that rejection. The two variable scopes are separate. -/
theorem unifier_not_refuted (query row : Term) (path : Path) (unifier : Unifies query row) :
    compatible (project query path) (project row path) = true := by
  obtain ⟨queryEnvironment, rowEnvironment, same⟩ := unifier
  by_cases unknownQuery : project query path = .unknown
  · simp [unknownQuery, compatible]
  by_cases unknownRow : project row path = .unknown
  · cases q : project query path <;> simp [unknownRow, compatible]
  have queryStable := known_projection_stable queryEnvironment query path unknownQuery
  have rowStable := known_projection_stable rowEnvironment row path unknownRow
  have observations := congrArg (fun term => project term path) same
  rw [queryStable, rowStable] at observations
  rw [observations]
  cases project row path <;> simp [compatible]

theorem stored_unifier_not_refuted (query row : Focus) (path : Path)
    (unifier : Unifies query.denote row.denote) :
    compatible (observe query path) (observe row path) = true := by
  rw [observe_correct, observe_correct]
  exact unifier_not_refuted _ _ _ unifier

def flat (kind : EndKind) (items : List Stored) : Stored :=
  .block items (.rigid (.ending kind))

namespace Controls

def value : Stored := .rigid (.symbol 3)
def exprEnd : Stored := .rigid (.ending .expression)
def listEnd : Stored := .rigid (.ending .listValue)
def arrayForm : Stored := flat .expression [value]
def cellForm : Stored := .cell value exprEnd
def openForm : Stored := .cell value (.var 0)

theorem same_value_different_storage : arrayForm.denote = cellForm.denote := by
  simp [arrayForm, cellForm, flat, exprEnd, denote_block, Stored.denote]

theorem observations_agree (path : Path) :
    observe (.value arrayForm) path = observe (.value cellForm) path :=
  representation_invariant (.value arrayForm) (.value cellForm) same_value_different_storage path

theorem open_tail_is_not_missing : observe (.value openForm) [.rest] = .unknown ∧
    observe (.value cellForm) [.rest, .first] = .absent := by
  rw [observe_correct, observe_correct]
  simp [Focus.denote, openForm, cellForm, value, exprEnd, Stored.denote, project]

theorem open_tail_can_match_closed : Unifies arrayForm.denote openForm.denote := by
  refine ⟨fun name => .var name, fun _ => .rigid (.ending .expression), ?_⟩
  simp [arrayForm, openForm, flat, value, denote_block, Stored.denote, substitute]

theorem typed_ending_stays_distinct :
    ¬ Unifies cellForm.denote (Stored.cell value listEnd).denote := by
  rintro ⟨queryEnvironment, rowEnvironment, same⟩
  simp [cellForm, value, exprEnd, listEnd, Stored.denote, substitute] at same

theorem unifiability_is_not_value_equality :
    Unifies (.var 0) (.rigid (.symbol 1)) ∧
      Unifies (.var 0) (.rigid (.symbol 2)) ∧
      ¬ Unifies (.rigid (.symbol 1)) (.rigid (.symbol 2)) := by
  refine ⟨⟨fun _ => .rigid (.symbol 1), fun name => .var name, rfl⟩,
    ⟨fun _ => .rigid (.symbol 2), fun name => .var name, rfl⟩, ?_⟩
  rintro ⟨_, _, same⟩
  cases same

end Controls

end Mettapedia.Machines.Cursor.SemanticTermView
