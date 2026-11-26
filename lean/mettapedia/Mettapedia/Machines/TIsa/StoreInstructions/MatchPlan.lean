import Mettapedia.Machines.TIsa.StoreInstructions.BindingSlots

/-!
# Flat path tests for an open first-order premise

The plan is compiled from the pattern alone. A path names a position
in the candidate, not a value supplied by the compiler. Each rigid
constructor is checked before descending into its arguments. A bind
reads the entire subterm at its path and checks the corresponding
variable slot. No later test can assume the success of an omitted
constructor check.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.MatchPlan

open Mettapedia.Logic.LP
open Derivation.FirstOrderTerms (Bindings extend)
open BindingSlots (Table Represents)

variable {σ : LPSignature}

abbrev Path := List ℕ
abbrev Symbol (σ : LPSignature) := Sum σ.constants σ.functionSymbols
abbrev Observation (σ : LPSignature) := Path → Option (GroundTerm σ)

def observe (root : GroundTerm σ) : Path → Option (GroundTerm σ)
  | [] => some root
  | i :: rest =>
    match root with
    | .const _ => none
    | .app f children => if inside : i < σ.functionArity f then observe (children ⟨i, inside⟩) rest else none

theorem observe_append (root : GroundTerm σ) (first later : Path) :
    observe root (first ++ later) = (observe root first).bind (fun atFirst => observe atFirst later) := by
  induction first generalizing root with
  | nil => simp [observe]
  | cons i path ih =>
    cases root with
    | const _ => rfl
    | app f children =>
      by_cases inside : i < σ.functionArity f <;> simp [observe, inside, ih]

def symbol : GroundTerm σ → Symbol σ
  | .const c => .inl c
  | .app f _ => .inr f

inductive Test (σ : LPSignature) where
  | shape (cursor : Path) (expected : Symbol σ)
  | bind (cursor : Path) (name : σ.vars)

/-- The candidate observations used by the two instruction shapes. -/
inductive Field where
  | tag (path : Path)
  | present (path : Path)
  | value (path : Path)
  deriving DecidableEq

def Test.fields : Test σ → List Field
  | .shape path _ => [.tag path]
  | .bind path _ => [.present path, .value path]

def demand (tests : List (Test σ)) : Finset Field := (tests.flatMap Test.fields).toFinset

theorem demand_covers {tests : List (Test σ)} {test : Test σ} (listed : test ∈ tests)
    {field : Field} (used : field ∈ test.fields) : field ∈ demand tests :=
  List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨test, listed, used⟩)

def children {f : σ.functionSymbols} (cursor : Path) (args : Fin (σ.functionArity f) → Term σ) :
    List (Path × Term σ) :=
  finToList (fun i => (cursor ++ [i.val], args i))

private theorem pattern_children {f : σ.functionSymbols} (cursor : Path) (args : Fin (σ.functionArity f) → Term σ) :
    (children cursor args).map Prod.snd = finToList args := by
  simp [children, finToList, List.map_map, Function.comp_def]

/-- Expansion uses depth-first, left-to-right argument order. -/
def compileForest : List (Path × Term σ) → List (Test σ)
  | [] => []
  | (cursor, .var v) :: later => .bind cursor v :: compileForest later
  | (cursor, .const c) :: later => .shape cursor (.inl c) :: compileForest later
  | (cursor, .app f args) :: later => .shape cursor (.inr f) :: compileForest (children cursor args ++ later)
termination_by phases => patternListSize (phases.map Prod.snd)
decreasing_by
  all_goals
    simp [List.map_append, pattern_children, patternListSize, Term.size, finToList, Fin.sum_univ_def,
      Function.comp_def, List.sum_append, List.map_map]

def compile (pattern : Term σ) : List (Test σ) := compileForest [([], pattern)]

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def shapePasses (read : Observation σ) (cursor : Path) (expected : Symbol σ) : Bool :=
  (read cursor).any (fun term => decide (symbol term = expected))

def collect (read : Observation σ) : List (Test σ) → Option (Bindings σ)
  | [] => some []
  | .shape cursor tag :: later => if shapePasses read cursor tag then collect read later else none
  | .bind cursor name :: later => do
    let found ← read cursor
    let tail ← collect read later
    pure ((name, found) :: tail)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem child_values {f : σ.functionSymbols} (cursor : Path)
    (patterns : Fin (σ.functionArity f) → Term σ) (values : Fin (σ.functionArity f) → GroundTerm σ)
    (root : GroundTerm σ) (located : observe root cursor = some (.app f values)) :
    (children cursor patterns).mapM (fun phase => observe root phase.1) = some (finToList values) := by
  unfold children finToList
  rw [List.mapM_map]
  have each : (fun i : Fin (σ.functionArity f) => observe root (cursor ++ [i.val])) = fun i => some (values i) := by
    funext i
    rw [observe_append, located, Option.bind_some]
    simp [observe, i.isLt]
  simp only [Function.comp_def, each]
  change (List.finRange (σ.functionArity f)).mapM (fun i => (pure (values i) : Option (GroundTerm σ))) =
    pure ((List.finRange (σ.functionArity f)).map values)
  exact List.mapM_pure

omit [DecidableEq σ.vars] in
/-- The compiled sequence accepts exactly the same constructor shape and
collects exactly the same list of binding occurrences. -/
theorem collect_forest (root : GroundTerm σ) :
    ∀ (phases : List (Path × Term σ)) (values : List (GroundTerm σ)),
      phases.mapM (fun phase => observe root phase.1) = some values →
      collect (observe root) (compileForest phases) = collectBindingsList (phases.map Prod.snd) values
  | [], _, found => by
    have same : [] = _ := Option.some.inj found
    rw [← same]
    simp [compileForest, collect, collectBindingsList]
  | (cursor, pattern) :: later, _, found => by
    rw [List.mapM_cons] at found
    obtain ⟨head, located, following⟩ := Option.bind_eq_some_iff.mp found
    change observe root cursor = some head at located
    obtain ⟨tail, ready, done⟩ := Option.bind_eq_some_iff.mp following
    have values := (Option.some.inj done).symm
    rw [values]
    cases pattern with
    | var v =>
      rw [compileForest, collect, located, collect_forest root later tail ready, List.map_cons, collectBindingsList]
      rfl
    | const c =>
      cases head with
      | const d =>
        by_cases same : c = d
        · subst d
          simpa only [compileForest, collect, shapePasses, located, Option.any_some, symbol, decide_true,
            if_true, List.map_cons, collectBindingsList] using collect_forest root later tail ready
        · simp [compileForest, collect, shapePasses, located, symbol, List.map_cons, collectBindingsList, same, Ne.symm same]
      | app g args => simp [compileForest, collect, shapePasses, located, symbol, List.map_cons, collectBindingsList]
    | app f patterns =>
      cases head with
      | const d => simp [compileForest, collect, shapePasses, located, symbol, List.map_cons, collectBindingsList]
      | app g args =>
        by_cases same : f = g
        · subst g
          have projected := child_values cursor patterns args root located
          have ready' : (children cursor patterns ++ later).mapM (fun phase => observe root phase.1) =
              some (finToList args ++ tail) := by
            rw [List.mapM_append, projected, ready]
            rfl
          have runs := collect_forest root (children cursor patterns ++ later) (finToList args ++ tail) ready'
          simpa only [compileForest, collect, shapePasses, located, Option.any_some, symbol, decide_true,
            if_true, List.map_cons, collectBindingsList, dif_pos True.intro, List.map_append, pattern_children] using runs
        · simp [compileForest, collect, shapePasses, located, symbol, List.map_cons, collectBindingsList, same, Ne.symm same]
termination_by phases _ _ => patternListSize (phases.map Prod.snd)
decreasing_by
  all_goals
    simp [List.map_append, pattern_children, patternListSize, Term.size, finToList, Fin.sum_univ_def,
      Function.comp_def, List.sum_append, List.map_map]

omit [DecidableEq σ.vars] in
theorem collect_compile (pattern : Term σ) (candidate : GroundTerm σ) :
    collect (observe candidate) (compile pattern) = collectBindings pattern candidate := by
  apply collect_forest candidate [([], pattern)] [candidate]
  simp [List.mapM_cons]
  rw [observe]
  rfl

/-- Operational order: each bind checks its slot immediately, before
the rest of the candidate is examined. -/
def run (read : Observation σ) : List (Test σ) → Table σ → Option (Table σ)
  | [], table => some table
  | .shape cursor tag :: later, table => if shapePasses read cursor tag then run read later table else none
  | .bind cursor name :: later, table => do
    let found ← read cursor
    let next ← BindingSlots.bind table name found
    run read later next

theorem run_cons (read : Observation σ) (first : Test σ) (later : List (Test σ)) (table : Table σ) :
    run read (first :: later) table = (run read [first] table).bind (run read later) := by
  cases first with
  | shape path tag =>
    by_cases fits : shapePasses read path tag = true <;> simp [run, fits]
  | bind path name =>
    cases found : read path with
    | none => simp [run, found]
    | some value =>
      cases bound : BindingSlots.bind table name value <;> simp [run, found, bound]

theorem run_eq_install (read : Observation σ) (tests : List (Test σ)) (table : Table σ) :
    run read tests table = (collect read tests).bind (BindingSlots.install table) := by
  induction tests generalizing table with
  | nil => rfl
  | cons first later ih =>
    cases first with
    | shape cursor tag =>
      by_cases fits : shapePasses read cursor tag = true <;> simp [run, collect, fits, ih]
    | bind cursor name =>
      cases value : read cursor with
      | none => simp [run, collect, value]
      | some found =>
        simp only [run, collect, value, bind, Option.bind_some]
        cases gathered : collect read later with
        | none =>
          cases checked : BindingSlots.bind table name found with
          | none => simp
          | some next => simp [ih, gathered]
        | some history => simp [BindingSlots.install, ih, gathered]

theorem run_compile (table : Table σ) (pattern : Term σ) (candidate : GroundTerm σ) :
    run (observe candidate) (compile pattern) table = BindingSlots.matchPattern table pattern candidate := by
  rw [run_eq_install, collect_compile]
  rfl

theorem run_accepts {table : Table σ} {history : Bindings σ} (view : Represents table history)
    (pattern : Term σ) (candidate : GroundTerm σ) :
    (run (observe candidate) (compile pattern) table).isSome = (extend history pattern candidate).isSome := by
  rw [run_compile]
  exact BindingSlots.matchPattern_accepts view pattern candidate

theorem run_represents {table after : Table σ} {history result : Bindings σ}
    (view : Represents table history) (pattern : Term σ) (candidate : GroundTerm σ)
    (ran : run (observe candidate) (compile pattern) table = some after)
    (reference : extend history pattern candidate = some result) : Represents after result := by
  rw [run_compile] at ran
  exact BindingSlots.matchPattern_represents view pattern candidate ran reference

namespace Examples

private abbrev atoms : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Bool
  functionArity := fun _ => 2

private instance : DecidableEq atoms.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.constants := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.functionSymbols := inferInstanceAs (DecidableEq Bool)

private def pattern : Term atoms :=
  .app true (fun i => if i.val = 0 then .var 0 else .app false (fun j => if j.val = 0 then .const 5 else .var 0))

private def tree (inner : Bool) (second : ℕ) : GroundTerm atoms :=
  .app true (fun i => if i.val = 0 then .const 7 else .app inner (fun j => if j.val = 0 then .const 5 else .const second))

private def empty : Table atoms := fun _ => none

theorem nested_repeated_variable_accepts : (run (observe (tree false 7)) (compile pattern) empty).isSome = true := by
  decide +kernel

theorem same_paths_cannot_hide_a_constructor_mismatch :
    (run (observe (tree true 7)) (compile pattern) empty).isNone = true := by
  decide +kernel

theorem nonadjacent_binding_conflict_refuses :
    (run (observe (tree false 8)) (compile pattern) empty).isNone = true := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.MatchPlan
