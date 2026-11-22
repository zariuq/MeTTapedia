import Mettapedia.Languages.MM0.OnTheStep.DeclarationProgram

/-!
# Files of sort declarations: the step accepts exactly what MM0's sort rule accepts

MM0's sort rule here is `declare`, written by hand after MM0's GSLT definition; no mechanical link to that
definition's files is proved.

For a file whose statements are sort declarations, run on the step by `DeclarationProgram.program` from the store
holding the file's row alone:

* **MM0's rule for sort declarations** (`declare`, `declareAll`), as MM0's GSLT definition has it
  (`sort_environment_v1`) and `mm0-rs` does: a sort whose name no sort has is declared with its modifiers; a name
  declared again with the same modifiers is accepted and changes nothing; a name declared again with other
  modifiers is refused. The environment is a list of names with their modifiers.
* **The theorem** (`accepted_reachable_iff`): rewriting of bags with absence reaches a bag holding `accepted` from
  the file's bag exactly when `declareAll [] ds` succeeds; on the step itself (`sorts_on_the_step`), for every
  state that reads as the file's bag (`AbsenceRewriting.reachable_iff_absent`), when identities are infinitely
  many. The direction "accepted only if well formed" is an invariant of every run (`Phase`, `phase_step`): the
  store is the cursor beside the rows of the environment of the statements read so far, then `accepted` beside
  the environment of the whole file; the twenty rules are checked one by one, and only `declareSort`,
  `repeatSort` and `acceptFile` can fire. The other direction builds the run (`runs_of_declareAll`).
* **Examples from MM0's test files** (`Examples`): upstream `tests/mm0_mmu/pass/sort.mm0` (sixteen sorts, every
  combination of modifiers) and CeTTa's `sort_repeated_identical.mm0` are accepted on the step; CeTTa's
  `sort_redeclared_conflict.mm0` (`provable sort wff; strict sort wff;`) is refused: no run reaches `accepted`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.SortDeclarations

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open NamesOnTheStep (Expr)
open Presentation.Schematic
open Machines (ReadsBag stepSystem listState listState_reads)
open AbsenceRewriting
open DeclarationProgram

universe uO

/-! ## Sort statements and MM0's rule -/

/-- **A sort statement** of the `.mm0` grammar: its four modifier trees and its name leaf. -/
structure SortStatement where
  pure : Expr
  strict : Expr
  provable : Expr
  free : Expr
  name : Expr

namespace SortStatement

/-- The tree of the statement (`statement_sort`, children in the order of the module's row). -/
def tree (d : SortStatement) : Expr := node "statement_sort" [d.pure, d.strict, d.provable, d.free, d.name]

/-- The four modifiers, as one row. -/
def mods (d : SortStatement) : Expr := modifiers d.pure d.strict d.provable d.free

end SortStatement

/-- **The tree of a file** of statements (`file_more`, `file_empty`). -/
def fileTree : List Expr → Expr
  | [] => node "file_empty" []
  | s :: ss => node "file_more" [s, fileTree ss]

/-- A sort environment: declared names with their modifiers, the latest first. -/
abbrev SortEnv := List (Expr × Expr)

/-- The modifiers a name is declared with, if any. -/
def lookupSort : SortEnv → Expr → Option Expr
  | [], _ => none
  | (s', m) :: env, s => if s' = s then some m else lookupSort env s

/-- **MM0's rule for one sort declaration**: a name no sort has is declared with its modifiers; a name declared
with the same modifiers is accepted and changes nothing; a name declared with other modifiers is refused. -/
def declare (env : SortEnv) (d : SortStatement) : Option SortEnv :=
  match lookupSort env d.name with
  | none => some ((d.name, d.mods) :: env)
  | some m => if m = d.mods then some env else none

/-- **MM0's rule for a list of sort declarations**, in order. -/
def declareAll : SortEnv → List SortStatement → Option SortEnv
  | env, [] => some env
  | env, d :: ds => (declare env d).bind fun env' => declareAll env' ds

/-- The rows of an environment: a name row and an entry row per declared sort. -/
def envRows : SortEnv → List Expr
  | [] => []
  | (s, m) :: env => sortName s :: sortEntry s m :: envRows env

/-- The bag of an environment. -/
abbrev envBag (env : SortEnv) : Multiset Expr := (envRows env : Multiset Expr)

/-- **The bag of a file**: its cursor row alone. -/
def start (ds : List SortStatement) : Multiset Expr :=
  (([pending (fileTree (ds.map SortStatement.tree))] : List Expr) : Multiset Expr)

/-! ## Environments -/

theorem lookupSort_eq_none_iff {s : Expr} : ∀ {env : SortEnv}, lookupSort env s = none ↔ s ∉ env.map Prod.fst
  | [] => by simp [lookupSort]
  | (s', m) :: env => by
      by_cases same : s' = s
      · subst same
        simp [lookupSort]
      · simp only [lookupSort, if_neg same, List.map_cons, List.mem_cons, not_or]
        rw [lookupSort_eq_none_iff (env := env)]
        exact ⟨fun absent => ⟨Ne.symm same, absent⟩, fun both => both.2⟩

theorem lookupSort_of_mem {s m : Expr} : ∀ {env : SortEnv}, (env.map Prod.fst).Nodup → (s, m) ∈ env →
    lookupSort env s = some m
  | [], _, inside => absurd inside List.not_mem_nil
  | (s', m') :: env, nodup, inside => by
      rcases List.mem_cons.mp inside with same | later
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        simp [lookupSort]
      · have notHere : s' ≠ s := by
          rintro rfl
          exact (List.nodup_cons.mp nodup).1 (List.mem_map.mpr ⟨(s', m), later, rfl⟩)
        simp only [lookupSort, if_neg notHere]
        exact lookupSort_of_mem (List.nodup_cons.mp nodup).2 later

theorem mem_of_lookupSort {s m : Expr} : ∀ {env : SortEnv}, lookupSort env s = some m → (s, m) ∈ env
  | [], found => by simp [lookupSort] at found
  | (s', m') :: env, found => by
      by_cases same : s' = s
      · simp only [lookupSort, if_pos same, Option.some.injEq] at found
        subst same
        subst found
        exact List.mem_cons_self
      · simp only [lookupSort, if_neg same] at found
        exact List.mem_cons_of_mem _ (mem_of_lookupSort found)

theorem declare_nodup {env env' : SortEnv} {d : SortStatement} (nodup : (env.map Prod.fst).Nodup)
    (declared : declare env d = some env') : (env'.map Prod.fst).Nodup := by
  cases found : lookupSort env d.name with
  | none =>
      have fresh : declare env d = some ((d.name, d.mods) :: env) := by simp [declare, found]
      rw [fresh] at declared
      cases declared
      exact List.nodup_cons.mpr ⟨lookupSort_eq_none_iff.mp found, nodup⟩
  | some m =>
      by_cases same : m = d.mods
      · have again : declare env d = some env := by simp [declare, found, same]
        rw [again] at declared
        cases declared
        exact nodup
      · have refused : declare env d = none := by simp [declare, found, same]
        rw [refused] at declared
        cases declared

theorem declareAll_nodup : ∀ {env env' : SortEnv} {ds : List SortStatement}, (env.map Prod.fst).Nodup →
    declareAll env ds = some env' → (env'.map Prod.fst).Nodup
  | _, _, [], nodup, done => by
      cases done
      exact nodup
  | env, env', d :: ds, nodup, done => by
      rw [show declareAll env (d :: ds) = (declare env d).bind (fun e => declareAll e ds) from rfl] at done
      cases declared : declare env d with
      | none =>
          rw [declared] at done
          cases done
      | some env'' =>
          rw [declared] at done
          exact declareAll_nodup (declare_nodup nodup declared) done

theorem declareAll_append : ∀ (env : SortEnv) (ds : List SortStatement) (d : SortStatement),
    declareAll env (ds ++ [d]) = (declareAll env ds).bind fun env' => declare env' d
  | env, [], d => by
      show (declare env d).bind (fun env' => some env') = declare env d
      cases declare env d <;> rfl
  | env, d' :: ds, d => by
      show (declare env d').bind (fun e => declareAll e (ds ++ [d])) =
        ((declare env d').bind fun e => declareAll e ds).bind fun e => declare e d
      cases declare env d' with
      | none => rfl
      | some env' => exact declareAll_append env' ds d

theorem mem_envRows {e : Expr} : ∀ {env : SortEnv}, e ∈ envRows env →
    (∃ s, e = sortName s ∧ s ∈ env.map Prod.fst) ∨ (∃ s m, e = sortEntry s m ∧ (s, m) ∈ env)
  | [], inside => absurd inside List.not_mem_nil
  | (s, m) :: env, inside => by
      rcases List.mem_cons.mp inside with rfl | inside
      · exact Or.inl ⟨s, rfl, List.mem_cons_self⟩
      rcases List.mem_cons.mp inside with rfl | inside
      · exact Or.inr ⟨s, m, rfl, List.mem_cons_self⟩
      rcases mem_envRows inside with ⟨s', rfl, known⟩ | ⟨s', m', rfl, known⟩
      · exact Or.inl ⟨s', rfl, List.mem_cons_of_mem _ known⟩
      · exact Or.inr ⟨s', m', rfl, List.mem_cons_of_mem _ known⟩

theorem kind_of_mem_envRows {e : Expr} {env : SortEnv} (inside : e ∈ envRows env) :
    kindOf e = some 1 ∨ kindOf e = some 2 := by
  rcases mem_envRows inside with ⟨s, rfl, -⟩ | ⟨s, m, rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem rows_of_mem {s m : Expr} : ∀ {env : SortEnv}, (s, m) ∈ env →
    sortName s ∈ envRows env ∧ sortEntry s m ∈ envRows env
  | [], inside => absurd inside List.not_mem_nil
  | (s', m') :: env, inside => by
      rcases List.mem_cons.mp inside with same | later
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · obtain ⟨named, entered⟩ := rows_of_mem later
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ named),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ entered)⟩

theorem sortName_mem_envRows {s : Expr} {env : SortEnv} : sortName s ∈ envRows env ↔ s ∈ env.map Prod.fst := by
  constructor
  · intro inside
    rcases mem_envRows inside with ⟨s', same, known⟩ | ⟨s', m', same, -⟩
    · rw [(List.cons.inj (row_inj.mp same).2).1]
      exact known
    · exact absurd (row_inj.mp same).1 (by decide)
  · intro inside
    obtain ⟨⟨s', m⟩, member, rfl⟩ := List.mem_map.mp inside
    exact (rows_of_mem member).1

theorem sortEntry_mem_envRows {s m : Expr} {env : SortEnv} : sortEntry s m ∈ envRows env ↔ (s, m) ∈ env := by
  constructor
  · intro inside
    rcases mem_envRows inside with ⟨s', same, -⟩ | ⟨s', m', same, known⟩
    · exact absurd (row_inj.mp same).1 (by decide)
    · obtain ⟨-, args⟩ := row_inj.mp same
      obtain ⟨sameName, rest⟩ := List.cons.inj args
      obtain ⟨sameMods, -⟩ := List.cons.inj rest
      rw [sameName, sameMods]
      exact known
  · exact fun inside => (rows_of_mem inside).2

/-! ## Bags -/

theorem mem_one_add {a x : Expr} {s : Multiset Expr} :
    x ∈ (([a] : List Expr) : Multiset Expr) + s ↔ x = a ∨ x ∈ s := by
  rw [Multiset.mem_add, Multiset.mem_coe, List.mem_singleton]

/-- The cursor is the only row of its kind beside an environment. -/
theorem pending_inv {G F : Expr} {rest : Multiset Expr} {env : SortEnv}
    (split : (([pending G] : List Expr) : Multiset Expr) + rest =
      (([pending F] : List Expr) : Multiset Expr) + envBag env) :
    G = F ∧ rest = envBag env := by
  have inside : pending G ∈ (([pending F] : List Expr) : Multiset Expr) + envBag env := by
    rw [← split]
    exact mem_one_add.mpr (Or.inl rfl)
  rcases mem_one_add.mp inside with same | there
  · have sameFile : G = F := (List.cons.inj (row_inj.mp same).2).1
    subst sameFile
    exact ⟨rfl, add_left_cancel split⟩
  · have kinds := kind_of_mem_envRows (Multiset.mem_coe.mp there)
    simp [pending] at kinds

/-- A row of kind `5` or more is no row of a cursor beside an environment. -/
theorem no_working_take {θ : ℕ → Expr} {k : ℕ} {args : List Tm} {rest : Multiset Expr} {F : Expr}
    {env : SortEnv}
    (split : (([inst θ (rowP k args)] : List Expr) : Multiset Expr) + rest =
      (([pending F] : List Expr) : Multiset Expr) + envBag env) (big : 5 ≤ k) : False := by
  have inside : inst θ (rowP k args) ∈ (([pending F] : List Expr) : Multiset Expr) + envBag env := by
    rw [← split]
    exact mem_one_add.mpr (Or.inl rfl)
  rw [inst_rowP] at inside
  rcases mem_one_add.mp inside with same | there
  · have := (row_inj.mp same).1
    omega
  · have kinds := kind_of_mem_envRows (Multiset.mem_coe.mp there)
    rw [kindOf_row] at kinds
    rcases kinds with same | same <;> (simp only [Option.some.injEq] at same; omega)

/-- No rule takes a row of `accepted` beside an environment. -/
theorem no_take_at_accepted {θ : ℕ → Expr} {k : ℕ} {args : List Tm} {rest : Multiset Expr} {env : SortEnv}
    (split : (([inst θ (rowP k args)] : List Expr) : Multiset Expr) + rest =
      (([accepted] : List Expr) : Multiset Expr) + envBag env) (kind : k = 0 ∨ 5 ≤ k) : False := by
  have inside : inst θ (rowP k args) ∈ (([accepted] : List Expr) : Multiset Expr) + envBag env := by
    rw [← split]
    exact mem_one_add.mpr (Or.inl rfl)
  rw [inst_rowP] at inside
  rcases mem_one_add.mp inside with same | there
  · have := (row_inj.mp same).1
    omega
  · have kinds := kind_of_mem_envRows (Multiset.mem_coe.mp there)
    rw [kindOf_row] at kinds
    rcases kinds with same | same <;> (simp only [Option.some.injEq] at same; omega)

theorem sort_statement_inv {a b c e f g : Expr} {d : SortStatement} {ds : List SortStatement}
    (same : node "file_more" [node "statement_sort" [a, b, c, e, f], g] =
      fileTree ((d :: ds).map SortStatement.tree)) :
    a = d.pure ∧ b = d.strict ∧ c = d.provable ∧ e = d.free ∧ f = d.name ∧
      g = fileTree (ds.map SortStatement.tree) := by
  obtain ⟨statement, rest⟩ := List.cons.inj (node_inj.mp same).2
  have fields := (node_inj.mp statement).2
  obtain ⟨samePure, fields⟩ := List.cons.inj fields
  obtain ⟨sameStrict, fields⟩ := List.cons.inj fields
  obtain ⟨sameProvable, fields⟩ := List.cons.inj fields
  obtain ⟨sameFree, fields⟩ := List.cons.inj fields
  obtain ⟨sameName, -⟩ := List.cons.inj fields
  exact ⟨samePure, sameStrict, sameProvable, sameFree, sameName, (List.cons.inj rest).1⟩

theorem declared_bag (s m r : Expr) (env : SortEnv) :
    (([sortName s, sortEntry s m, pending r] : List Expr) : Multiset Expr) + envBag env =
      (([pending r] : List Expr) : Multiset Expr) + envBag ((s, m) :: env) := by
  simp only [envBag, envRows, ← Multiset.cons_coe, Multiset.cons_add, Multiset.coe_nil, zero_add]
  rw [Multiset.cons_swap (pending r) (sortName s), Multiset.cons_swap (pending r) (sortEntry s m)]

/-! ## The invariant of every run -/

/-- **Where a run from a file of sort statements can be**: the cursor at the rest of the file beside the
environment of the statements before it, which MM0's rule accepts; or `accepted` beside the environment of the
whole file, which MM0's rule accepts. -/
def Phase (ds₀ : List SortStatement) (bag : Multiset Expr) : Prop :=
  (∃ done rest env, ds₀ = done ++ rest ∧ declareAll [] done = some env ∧
      bag = (([pending (fileTree (rest.map SortStatement.tree))] : List Expr) : Multiset Expr) + envBag env) ∨
    (∃ env, declareAll [] ds₀ = some env ∧ bag = (([accepted] : List Expr) : Multiset Expr) + envBag env)

theorem phase_start (ds₀ : List SortStatement) : Phase ds₀ (start ds₀) :=
  Or.inl ⟨[], ds₀, [], rfl, rfl, (add_zero _).symm⟩

/-- **Every rewrite keeps the invariant.** -/
theorem phase_step {ds₀ : List SortStatement} {bag bag' : Multiset Expr} (phase : Phase ds₀ bag)
    (step : RewritesAbsent program bag bag') : Phase ds₀ bag' := by
  obtain ⟨r, member, θ, rest, split, readsIn, -, absences, rfl⟩ := step
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases phase with ⟨done, rest₀, env, decomposed, checked, rfl⟩ | ⟨env, checked, rfl⟩
  · rcases member with rfl | rfl | rfl | rfl | member
    · -- declareSort
      rw [show declareSort.body.take.map (inst θ) =
          [pending (node "file_more" [node "statement_sort" [θ 0, θ 1, θ 2, θ 3, θ 4], θ 5])] from rfl] at split
      obtain ⟨sameFile, rfl⟩ := pending_inv split
      cases rest₀ with
      | nil => exact absurd (node_inj.mp sameFile).1 (by decide)
      | cons d ds =>
          obtain ⟨hp, hst, hpr, hf, hs, hr⟩ := sort_statement_inv sameFile
          have fresh : sortName (θ 4) ∉ (([pending (fileTree ((d :: ds).map SortStatement.tree))] : List Expr) :
              Multiset Expr) + envBag env :=
            absences (rowP 1 [u 4]) (List.mem_singleton_self _)
          have unnamed : sortName d.name ∉ envRows env := fun inside =>
            fresh (mem_one_add.mpr (Or.inr (by rw [hs]; exact Multiset.mem_coe.mpr inside)))
          have looked : lookupSort env d.name = none :=
            lookupSort_eq_none_iff.mpr fun known => unnamed (sortName_mem_envRows.mpr known)
          have declared : declare env d = some ((d.name, d.mods) :: env) := by simp [declare, looked]
          refine Or.inl ⟨done ++ [d], ds, (d.name, d.mods) :: env,
            by rw [decomposed, List.append_assoc, List.singleton_append],
            by rw [declareAll_append, checked]; exact declared, ?_⟩
          show (([sortName (θ 4), sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)), pending (θ 5)] :
              List Expr) : Multiset Expr) + envBag env = _
          rw [hp, hst, hpr, hf, hs, hr]
          exact declared_bag _ _ _ env
    · -- repeatSort
      rw [show repeatSort.body.take.map (inst θ) =
          [pending (node "file_more" [node "statement_sort" [θ 0, θ 1, θ 2, θ 3, θ 4], θ 5])] from rfl] at split
      obtain ⟨sameFile, rfl⟩ := pending_inv split
      cases rest₀ with
      | nil => exact absurd (node_inj.mp sameFile).1 (by decide)
      | cons d ds =>
          obtain ⟨hp, hst, hpr, hf, hs, hr⟩ := sort_statement_inv sameFile
          have known : sortEntry (θ 4) (modifiers (θ 0) (θ 1) (θ 2) (θ 3)) ∈ envBag env :=
            readsIn (rowP 2 [u 4, listP [u 0, u 1, u 2, u 3]]) (List.mem_singleton_self _)
          rw [hp, hst, hpr, hf, hs] at known
          have entered : (d.name, d.mods) ∈ env := sortEntry_mem_envRows.mp (Multiset.mem_coe.mp known)
          have nodup := declareAll_nodup (env := []) List.nodup_nil checked
          have declared : declare env d = some env := by simp [declare, lookupSort_of_mem nodup entered]
          refine Or.inl ⟨done ++ [d], ds, env, by rw [decomposed, List.append_assoc, List.singleton_append],
            by rw [declareAll_append, checked]; exact declared, ?_⟩
          show (([pending (θ 5)] : List Expr) : Multiset Expr) + envBag env = _
          rw [hr]
    · -- acceptFile
      rw [show acceptFile.body.take.map (inst θ) = [pending (node "file_empty" [])] from rfl] at split
      obtain ⟨sameFile, rfl⟩ := pending_inv split
      cases rest₀ with
      | nil =>
          refine Or.inr ⟨env, by rw [decomposed, List.append_nil]; exact checked, rfl⟩
      | cons d ds => exact absurd (node_inj.mp sameFile).1 (by decide)
    · -- startTerm
      rw [show startTerm.body.take.map (inst θ) =
          [pending (node "file_more" [node "statement_term" [θ 0, θ 1, θ 2], θ 3])] from rfl] at split
      obtain ⟨sameFile, -⟩ := pending_inv split
      cases rest₀ with
      | nil => exact absurd (node_inj.mp sameFile).1 (by decide)
      | cons d ds =>
          have statement := (List.cons.inj (node_inj.mp sameFile).2).1
          exact absurd (node_inj.mp statement).1 (by decide)
    · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> exact (no_working_take split (by decide)).elim
  · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact (no_take_at_accepted split (by decide)).elim

theorem phase_multi {ds₀ : List SortStatement} : ∀ {bag bag' : (rewritingAbsent program).Term},
    (rewritingAbsent program).MultiStep bag bag' → Phase ds₀ bag → Phase ds₀ bag'
  | _, _, .refl _, phase => phase
  | _, _, .step first rest, phase => phase_multi rest (phase_step phase first)

theorem accepted_of_phase {ds₀ : List SortStatement} {bag : Multiset Expr} (phase : Phase ds₀ bag)
    (inside : accepted ∈ bag) : (declareAll [] ds₀).isSome := by
  rcases phase with ⟨done, rest, env, -, -, rfl⟩ | ⟨env, checked, -⟩
  · rcases mem_one_add.mp inside with same | there
    · exact absurd (row_inj.mp same).1 (by decide)
    · have kinds := kind_of_mem_envRows (Multiset.mem_coe.mp there)
      simp [accepted] at kinds
  · simp [checked]

/-! ## The runs -/

theorem runs_of_declareAll : ∀ (ds : List SortStatement) (env env' : SortEnv), declareAll env ds = some env' →
    (rewritingAbsent program).MultiStep
      ((([pending (fileTree (ds.map SortStatement.tree))] : List Expr) : Multiset Expr) + envBag env)
      ((([accepted] : List Expr) : Multiset Expr) + envBag env')
  | [], env, env', done => by
      cases done
      exact .step (acceptFile_fires (envBag env)) (.refl _)
  | d :: ds, env, env', done => by
      rw [show declareAll env (d :: ds) = (declare env d).bind (fun e => declareAll e ds) from rfl] at done
      cases declared : declare env d with
      | none =>
          rw [declared] at done
          cases done
      | some env'' =>
          rw [declared] at done
          have rest := runs_of_declareAll ds env'' env' done
          cases found : lookupSort env d.name with
          | none =>
              have fresh : declare env d = some ((d.name, d.mods) :: env) := by simp [declare, found]
              rw [fresh] at declared
              cases declared
              have fresh : sortName d.name ∉ (([pending (node "file_more" [node "statement_sort"
                  [d.pure, d.strict, d.provable, d.free, d.name], fileTree (ds.map SortStatement.tree)])] :
                  List Expr) : Multiset Expr) + envBag env := by
                intro inside
                rcases mem_one_add.mp inside with same | there
                · exact absurd (row_inj.mp same).1 (by decide)
                · exact lookupSort_eq_none_iff.mp found (sortName_mem_envRows.mp (Multiset.mem_coe.mp there))
              have first := declareSort_fires d.pure d.strict d.provable d.free d.name
                (fileTree (ds.map SortStatement.tree)) (envBag env) fresh
              rw [declared_bag] at first
              exact .step first rest
          | some m =>
              by_cases same : m = d.mods
              · have again : declare env d = some env := by simp [declare, found, same]
                rw [again] at declared
                cases declared
                have known : sortEntry d.name d.mods ∈ envBag env := by
                  rw [← same]
                  exact Multiset.mem_coe.mpr (rows_of_mem (mem_of_lookupSort found)).2
                exact .step (repeatSort_fires d.pure d.strict d.provable d.free d.name
                  (fileTree (ds.map SortStatement.tree)) (envBag env) known) rest
              · have refused : declare env d = none := by simp [declare, found, same]
                rw [refused] at declared
                cases declared

/-! ## The theorem -/

/-- **A file of sort declarations reaches `accepted` exactly when MM0's rule accepts it**, by rewriting of bags
with absence. -/
theorem accepted_reachable_iff (ds : List SortStatement) :
    (∃ bag : Multiset Expr, (rewritingAbsent program).MultiStep (start ds) bag ∧ accepted ∈ bag) ↔
      (declareAll [] ds).isSome := by
  constructor
  · rintro ⟨bag, steps, inside⟩
    exact accepted_of_phase (phase_multi steps (phase_start ds)) inside
  · intro checked
    obtain ⟨env, done⟩ := Option.isSome_iff_exists.mp checked
    refine ⟨(([accepted] : List Expr) : Multiset Expr) + envBag env, ?_, mem_one_add.mpr (Or.inl rfl)⟩
    have runs := runs_of_declareAll ds [] env done
    rw [show envBag [] = 0 from rfl, add_zero] at runs
    exact runs

/-- **On the step**: from every state that reads as the bag of a file of sort declarations, the step reaches a
state that reads as a bag holding `accepted` exactly when MM0's rule accepts the file. -/
theorem sorts_on_the_step {O : Type uO} [DecidableEq O] [Infinite O] (ds : List SortStatement) {s : SState O}
    (reads : ReadsBag s (start ds)) :
    (∃ s', (stepSystem O program).MultiStep s s' ∧ ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag) ↔
      (declareAll [] ds).isSome :=
  (reachable_iff_absent program_fragment (fun bag => accepted ∈ bag) reads).symm.trans (accepted_reachable_iff ds)

/-- The state of a file's row reads as the file's bag, so the theorem is about something. -/
theorem start_reads (ds : List SortStatement) :
    ReadsBag (listState [pending (fileTree (ds.map SortStatement.tree))]) (start ds) :=
  listState_reads _

/-! ## Examples from MM0's test files -/

namespace Examples

/-- An identifier leaf. -/
def ident (text : String) : Expr := leaf "id_tok" text

/-- A sort statement with its modifiers given as presence (the trees `pure_yes`/`pure_no` and so on). -/
def sortStmt (pure strict provable free : Bool) (name : String) : SortStatement :=
  ⟨if pure then node "pure_yes" [] else node "pure_no" [],
    if strict then node "strict_yes" [] else node "strict_no" [],
    if provable then node "provable_yes" [] else node "provable_no" [],
    if free then node "free_yes" [] else node "free_no" [], ident name⟩

/-- **Upstream `tests/mm0_mmu/pass/sort.mm0`**: sixteen sorts, every combination of the four modifiers. -/
def upstreamSorts : List SortStatement :=
  [sortStmt false false false false "s0", sortStmt false false false true "s1",
    sortStmt false false true false "s2", sortStmt false false true true "s3",
    sortStmt false true false false "s4", sortStmt false true false true "s5",
    sortStmt false true true false "s6", sortStmt false true true true "s7",
    sortStmt true false false false "s8", sortStmt true false false true "s9",
    sortStmt true false true false "s10", sortStmt true false true true "s11",
    sortStmt true true false false "s12", sortStmt true true false true "s13",
    sortStmt true true true false "s14", sortStmt true true true true "s15"]

/-- **CeTTa's `tests/langdef/mm0/sort_repeated_identical.mm0`**:
`provable sort wff; provable sort wff; strict sort set;`. -/
def repeatedIdentical : List SortStatement :=
  [sortStmt false false true false "wff", sortStmt false false true false "wff",
    sortStmt false true false false "set"]

/-- **CeTTa's `tests/langdef/mm0/sort_redeclared_conflict.mm0`**: `provable sort wff; strict sort wff;`. -/
def redeclaredConflict : List SortStatement :=
  [sortStmt false false true false "wff", sortStmt false true false false "wff"]

theorem upstreamSorts_checked : (declareAll [] upstreamSorts).isSome = true := by decide +kernel

theorem repeatedIdentical_checked : (declareAll [] repeatedIdentical).isSome = true := by decide +kernel

theorem redeclaredConflict_refused : (declareAll [] redeclaredConflict).isSome = false := by decide +kernel

/-- **The sixteen sorts are accepted on the step.** -/
theorem upstreamSorts_on_the_step :
    ∃ s', (stepSystem ℕ program).MultiStep (listState [pending (fileTree (upstreamSorts.map SortStatement.tree))])
      s' ∧ ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag :=
  (sorts_on_the_step upstreamSorts (start_reads upstreamSorts)).mpr upstreamSorts_checked

/-- **The identical redeclaration is accepted on the step.** -/
theorem repeatedIdentical_on_the_step :
    ∃ s', (stepSystem ℕ program).MultiStep
      (listState [pending (fileTree (repeatedIdentical.map SortStatement.tree))]) s' ∧
        ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag :=
  (sorts_on_the_step repeatedIdentical (start_reads repeatedIdentical)).mpr repeatedIdentical_checked

/-- **The conflicting redeclaration is refused on the step**: no run reaches a state that reads as a bag holding
`accepted`. -/
theorem redeclaredConflict_refused_on_the_step :
    ¬ ∃ s', (stepSystem ℕ program).MultiStep
      (listState [pending (fileTree (redeclaredConflict.map SortStatement.tree))]) s' ∧
        ∃ bag, ReadsBag s' bag ∧ accepted ∈ bag := by
  rw [sorts_on_the_step redeclaredConflict (start_reads redeclaredConflict), redeclaredConflict_refused]
  decide

end Examples

#print axioms phase_step
#print axioms runs_of_declareAll
#print axioms accepted_reachable_iff
#print axioms sorts_on_the_step
#print axioms Examples.upstreamSorts_on_the_step
#print axioms Examples.repeatedIdentical_on_the_step
#print axioms Examples.redeclaredConflict_refused_on_the_step

end Mettapedia.Languages.MM0.OnTheStep.SortDeclarations
