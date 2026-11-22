import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Presentations

/-!
# Control: a presentation with one store term and a freshness premise over it

The separation is about translations homomorphic on parallel composition. A presentation whose one
term holds the whole store can test that whole term in one premise.

`ownedStore` has one constructor, `Store`, holding a bag of rows, and one rule, `SpawnIfAbsent`:
`Store {...rows} ~> Store {T, ...rows}` provided the name `U` occurs nowhere in the rows. The
premise is the format's freshness premise, an occurs check of a name over a term.

* `ownedStore_step_iff`: from a store term, the reduction adds `T` **exactly when the name `U` occurs
  nowhere in the rows**, under the engine's premise evaluator with every relation environment.
* **An occurs check, not a test of rows** (`nested_blocks`, `other_fires`): at the store whose only
  row is `g(U)`, no row is `U` and the rule does not fire; at the store whose only row is `h`, it
  fires. The absence check of the step reads rows: a row that mentions `U` without being `U` does not
  refuse it.
* `ownedStore_no_parallelContextRule`: the presentation has no parallel context rule, so the
  relation-level theorem does not apply to it, as it must not.

No translation of the step into this presentation is stated here. A presentation whose rule tests the
rows is `RuleSyntax.Presentation.wholeStore`: its one rewrite makes `12` where no row of the store is
`11`, by a premise that asks a relation environment deciding that of the bag; read on composition
terms its step is exactly the absence step (`RuleSyntax.Presentation.whole_presents_absence`). The
translation of the absence-guarded step into it, built from the rows, is `Interpreter.interpret`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.OwnedStore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv
  premiseStepWithEnv_freshness_check premiseStepWithEnv_freshness_mem)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Substitution (isFresh checkFreshness freeVars)

/-- A store term: one `Store` holding a bag of rows. -/
def store (rows : List Pattern) : Pattern := .apply "Store" [.collection .hashBag rows none]

/-- The row `T`. -/
def madeRow : Pattern := .apply "T" []

/-- The whole store, as a pattern binding its rows to `rows`. -/
def storeRows : Pattern := .collection .hashBag [] (some "rows")

/-- **Make `T` where the name `U` is absent from the whole store.** -/
def spawnIfAbsent : RewriteRule where
  name := "SpawnIfAbsent"
  typeContext := []
  premises := [.freshness ⟨"U", storeRows⟩]
  left := .apply "Store" [storeRows]
  right := .apply "Store" [.collection .hashBag [madeRow] (some "rows")]

/-- The store constructor. -/
def storeConstructor : GrammarRule where
  label := "Store"
  category := "Store"
  params := [.simple "rows" (TypeExpr.bag (.base "Row"))]
  syntaxPattern := [.terminal "[", .nonTerminal "rows", .separator ",", .terminal "]"]

/-- **The owned-store presentation.** -/
def ownedStore : LanguageDef where
  name := "OwnedStore"
  types := ["Store", "Row"]
  terms := [storeConstructor]
  equations := []
  rewrites := [spawnIfAbsent]

/-- The bindings of a store term. -/
abbrev rowsBinding (rows : List Pattern) : Bindings := [("rows", .collection .hashBag rows none)]

/-- The rule's left side matches a store term, binding its rows. -/
theorem store_match (rows : List Pattern) :
    rowsBinding rows ∈ matchPattern spawnIfAbsent.left (store rows) :=
  matchPattern_iff_matchRel.mpr
    (.apply (.cons (.collection (by decide) .nilRest) .nil (by simp [mergeBindings])) rfl)

/-- That is the only match. -/
theorem store_match_unique {rows : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern spawnIfAbsent.left (store rows)) :
    bindings = rowsBinding rows := by
  have relation := matchPattern_iff_matchRel.mp matched
  cases relation with
  | apply arguments _ =>
      cases arguments with
      | cons head tail merged =>
          cases tail
          cases head with
          | collection _ bag =>
              cases bag
              simpa [mergeBindings] using merged.symm

/-- The rows of a store term, read through the rule's pattern. -/
theorem applyBindings_storeRows (rows : List Pattern) :
    applyBindings (rowsBinding rows) storeRows = .collection .hashBag rows none := by
  simp [applyBindings, storeRows]

/-- **The freshness premise reads the whole store.** -/
theorem freshness_premise (relEnv : RelationEnv) (rows : List Pattern) :
    premiseStepWithEnv relEnv ownedStore (rowsBinding rows) (.freshness ⟨"U", storeRows⟩) =
      if checkFreshness ⟨"U", applyBindings (rowsBinding rows) storeRows⟩ then
        [rowsBinding rows] else [] := rfl

/-- The contractum of the rule at a store term. -/
theorem contractum (rows : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule ownedStore spawnIfAbsent
      (rowsBinding rows) = store (madeRow :: rows) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
  simp [applyBindings, spawnIfAbsent, store, madeRow]

/-- **The rule fires exactly when the name `U` occurs nowhere in the store's rows**: from a store
term, the reduction adds `T` exactly then. -/
theorem ownedStore_step_iff (relEnv : RelationEnv) (rows : List Pattern) (result : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) ownedStore
        (store rows) result ↔
      isFresh "U" (.collection .hashBag rows none) = true ∧ result = store (madeRow :: rows) := by
  constructor
  · rintro ⟨fuel, step⟩
    cases step with
    | rule member matched premises applied =>
        simp only [ownedStore, List.mem_singleton] at member
        subst member
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
        have initial := store_match_unique matched
        subst initial
        cases premises with
        | cons first rest =>
            cases rest
            cases first with
            | freshness evaluated =>
                change _ ∈ premiseStepWithEnv relEnv ownedStore (rowsBinding rows)
                  (.freshness ⟨"U", storeRows⟩) at evaluated
                have kept := premiseStepWithEnv_freshness_mem evaluated
                obtain ⟨name, resolved, fresh⟩ := premiseStepWithEnv_freshness_check evaluated
                have named : name = "U" := by
                  simp [Bindings.lookup] at resolved
                  exact resolved.symm
                subst named kept
                rw [applyBindings_storeRows] at fresh
                exact ⟨fresh, (contractum rows).symm.trans applied |>.symm⟩
  · rintro ⟨fresh, rfl⟩
    refine ⟨1, .rule (rule := spawnIfAbsent) (initialBindings := rowsBinding rows)
      (finalBindings := rowsBinding rows)
      (by simp [ownedStore]) ?_ (.cons (.freshness ?_) (.nil _)) (contractum rows)⟩
    · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      exact store_match rows
    · change rowsBinding rows ∈ premiseStepWithEnv relEnv ownedStore (rowsBinding rows)
        (.freshness ⟨"U", storeRows⟩)
      rw [freshness_premise, applyBindings_storeRows]
      simp [checkFreshness, fresh]

/-- **Examples.** It adds `T` to the empty store, and never fires at a store holding `U`. -/
theorem ownedStore_examples (relEnv : RelationEnv) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) ownedStore
        (store []) (store [madeRow]) ∧
      ∀ result, ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) ownedStore
        (store [.fvar "U"]) result :=
  ⟨(ownedStore_step_iff relEnv [] _).mpr ⟨by simp [isFresh, freeVars], rfl⟩,
    fun result step => by
      have fresh := ((ownedStore_step_iff relEnv [.fvar "U"] result).mp step).1
      simp [isFresh, freeVars] at fresh⟩

/-- A row that mentions the name `U` without being `U`. -/
def nestedRow : Pattern := .apply "g" [.fvar "U"]

/-- A row that does not mention `U`. -/
def otherRow : Pattern := .apply "h" []

/-- **An occurs check, not a test of rows**: no row of the store `[g(U)]` is `U`, and the rule does
not fire there. -/
theorem nested_blocks (relEnv : RelationEnv) :
    (∀ r ∈ [nestedRow], r ≠ .fvar "U") ∧
      ∀ result, ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) ownedStore
        (store [nestedRow]) result := by
  refine ⟨fun r member => ?_, fun result step => ?_⟩
  · simp only [List.mem_singleton] at member
    subst member
    simp [nestedRow]
  · have fresh := ((ownedStore_step_iff relEnv [nestedRow] result).mp step).1
    simp [isFresh, freeVars, nestedRow] at fresh

/-- **Positive control**: at the store `[h]` the rule fires. -/
theorem other_fires (relEnv : RelationEnv) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) ownedStore
      (store [otherRow]) (store [madeRow, otherRow]) :=
  (ownedStore_step_iff relEnv [otherRow] _).mpr ⟨by simp [isFresh, freeVars, otherRow], rfl⟩

/-- **The owned store has no parallel context rule**: its one rule asks a freshness premise. -/
theorem ownedStore_no_parallelContextRule (kind : CollType) :
    ¬ HasParallelContextRule kind ownedStore := by
  rintro ⟨rule, member, source, target, rest, _, _, _, premises, _, _⟩
  simp only [ownedStore, List.mem_singleton] at member
  subst member
  simp [spawnIfAbsent] at premises

#print axioms store_match_unique
#print axioms freshness_premise
#print axioms contractum
#print axioms ownedStore_step_iff
#print axioms ownedStore_examples
#print axioms nested_blocks
#print axioms other_fires
#print axioms ownedStore_no_parallelContextRule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.OwnedStore
