import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.OSLF.MeTTaIL.RuleInstances
import Mettapedia.OSLF.MeTTaIL.BindingAgreement
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# A program as a language definition

A program over rows (`Rule Rows`, rules at the one frame over `Expr`) is presented as a five-field
language definition of the tree's framework (`present`):

* **sorts** `Nat`, `Row`, `Store`;
* **constructors**: the row formers and the union of stores, a bag of rows (`Rows`);
* **no equations**: the only equations are the ones the framework derives from the declared bag, its
  permutations;
* **one rewrite per rule** (`rewriteWith`), with no premise: what the rule consumes, beside a rest, becomes
  what it yields, beside the same rest. The rest variable is the parallel context of the rewrite, as in the
  framework's own COMM rule for rho. A rule of the fragment has ground guards; it is presented when they
  hold (`guardsHold`), and has no rewrite otherwise.

What a rule consumes and yields is a **reading** (`Reading`). The step's own reading (`standard`) consumes
the takes and the reads without repetition (`consumes`) and yields the made rows and the same reads
(`yields`): reads keep their rows, and two reads may read one row, while takes may not share. The naive
reading (`naive`) lists every read; `Possibility.Controls` shows it presents a different step.

**The fragment** (`Positive`): every check is an equation guard, and the rule has no collect pattern. Rules
with none queries or count checks, or with collect patterns, are outside it.

What is proved here about the framework's step on stores, for every reading:
* `step_storeCode`: a primitive step of the presented language from a store is a rule whose consumed rows
  are part of the store, to the store with them replaced by its yielded rows; `step_prefix` is the converse
  at the arrangement with the consumed rows first;
* `semanticStep_storeCode_iff`: **the framework's step modulo equations** (`langSemanticReducesUsing`, the
  relation OSLF consumes) from a store is exactly such a rule, up to the equations at the target;
* `diamond_storeCode_iff`: **the framework's generated possibility** (`langDiamondUsing`) at a store;
* `semanticStep_beside`: **the parallel context rule holds**: a step of a store is a step of the store
  beside any further rows.
No premise is used anywhere: every rewrite has the empty premise list (`presentWith_plain`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PlainRules step_iff_exists_match)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing langDiamondUsing langDiamondUsing_spec
  langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations)
open NamesOnTheStep (Expr)

/-- Terms at the one frame, over rows. -/
abbrev Rows := OneFrame.Terms Expr

/-! ## The fragment -/

/-- An equation guard. -/
def isEquationCheck : Check Expr → Bool
  | .equal _ _ => true
  | _ => false

/-- **The positive fragment**: every check is an equation guard, and no collect pattern. -/
def Positive (r : Rule Rows) : Prop := r.collect = [] ∧ r.body.checks.all isEquationCheck = true

instance (r : Rule Rows) : Decidable (Positive r) := by
  unfold Positive
  infer_instance

/-- A check of a ground rule holds when its sides are identical. The none query and count checks are not decided
here: they are outside the fragment. -/
def groundCheck : Check Expr → Bool
  | .equal left right => decide (left = right)
  | _ => true

/-- **The guards of a ground rule hold**: every told equation and every equation guard has identical sides. -/
def guardsHold (r : Rule Rows) : Bool :=
  r.body.tell.all (fun e => decide (e.1 = e.2)) && r.body.checks.all groundCheck

/-- **What a rule consumes**: its takes, and its reads without repetition. -/
def consumes (r : Rule Rows) : List Expr := r.body.take ++ r.body.read.dedup

/-- **What a rule yields**: its made rows, and its reads without repetition. -/
def yields (r : Rule Rows) : List Expr := r.body.produce ++ r.body.read.dedup

/-- **A reading of rules**: what each rule consumes and what it yields. -/
structure Reading where
  consumed : Rule Rows → List Expr
  yielded : Rule Rows → List Expr

/-- **The step's reading**: takes and distinct reads are consumed; made rows and the same reads are yielded. -/
def standard : Reading := ⟨consumes, yields⟩

/-- **The naive reading**: every read is a separate row. -/
def naive : Reading := ⟨fun r => r.body.take ++ r.body.read, fun r => r.body.produce ++ r.body.read⟩

/-! ## The presentation -/

/-- Rows beside the parallel context `rest`. -/
def besideRest (rows : List Expr) : Pattern := .collection .hashBag (rows.map rowCode) (some "rest")

/-- **The rewrite of a rule**: what it consumes beside a rest becomes what it yields beside the same rest. -/
def rewriteWith (R : Reading) (r : Rule Rows) : RewriteRule where
  name := "Fire"
  typeContext := [("rest", .bag (.base "Row"))]
  premises := []
  left := besideRest (R.consumed r)
  right := besideRest (R.yielded r)

/-- The rewrite of a rule, named by its position among the presented rules. -/
def namedRewrite (R : Reading) (index : ℕ) (r : Rule Rows) : RewriteRule :=
  { rewriteWith R r with name := "Fire" ++ toString index }

/-- **The presentation of a program under a reading**: the sorts of numerals, rows and stores; the row formers
and the union of stores; no equations; one rewrite per rule whose guards hold. -/
def presentWith (R : Reading) (rules : List (Rule Rows)) : LanguageDef where
  name := "StepOfAProgram"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := (rules.filter guardsHold).mapIdx fun index r => namedRewrite R index r

/-- **The presentation of a program**, under the step's reading. -/
abbrev present (rules : List (Rule Rows)) : LanguageDef := presentWith standard rules

variable {R : Reading} {rules : List (Rule Rows)}

theorem presentWith_equations : (presentWith R rules).equations = [] := rfl

theorem presentWith_noAlgebra : (presentWith R rules).hasAlgebraDeclarations = false := rfl

theorem presentWith_formers : rowFormers ⊆ (presentWith R rules).terms := List.subset_append_left _ _

theorem presentWith_store : storeFormer ∈ (presentWith R rules).terms :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- **Every rewrite of the presentation is the rewrite of a rule whose guards hold.** -/
theorem of_mem_rewrites {rule : RewriteRule} (member : rule ∈ (presentWith R rules).rewrites) :
    ∃ r ∈ rules, guardsHold r = true ∧ ∃ index, namedRewrite R index r = rule := by
  obtain ⟨index, bound, named⟩ := List.mem_mapIdx.mp member
  have inside := List.getElem_mem bound
  rw [List.mem_filter] at inside
  exact ⟨_, inside.1, inside.2, index, named⟩

/-- **Every rule whose guards hold has its rewrite in the presentation.** -/
theorem exists_mem_rewrites {r : Rule Rows} (member : r ∈ rules) (holds : guardsHold r = true) :
    ∃ index, namedRewrite R index r ∈ (presentWith R rules).rewrites := by
  obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp (List.mem_filter.mpr ⟨member, holds⟩)
  exact ⟨index, List.mem_mapIdx.mpr ⟨index, bound, by rw [found]⟩⟩

theorem binderFree_besideRest (rows : List Expr) : binderFree (besideRest rows) = true := by
  show binderFreeList (rows.map rowCode) = true
  exact binderFreeList_rows rows

/-- **No rewrite of the presentation has a premise**, and none moves a metavariable across a binder. -/
theorem presentWith_plain : PlainRules (presentWith R rules) := by
  intro rule member
  obtain ⟨r, -, -, index, rfl⟩ := of_mem_rewrites member
  exact ⟨rfl, ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _)⟩

/-! ## Matching a rule against a store -/

theorem mergeBindings_single (name : String) (value : Pattern) :
    mergeBindings [] [(name, value)] = some [(name, value)] := rfl

/-- **A rule's rows match a store only where the store permutes them beside a remainder**, which the rest
captures. -/
theorem matchBag_rows {rest : String} : ∀ {rows : List Expr} {terms : List Pattern} {bindings : Bindings},
    MatchBagRel (rows.map rowCode) (some rest) .hashBag terms bindings →
      ∃ remainder, (rows.map rowCode ++ remainder).Perm terms ∧
        bindings = [(rest, .collection .hashBag remainder none)]
  | [], terms, bindings, matched => by
      simp only [List.map_nil] at matched
      cases matched
      exact ⟨terms, .refl _, rfl⟩
  | e :: rows, terms, bindings, matched => by
      rw [List.map_cons] at matched
      cases matched with
      | cons index bound head tail merged =>
          obtain ⟨found, rfl⟩ := rigid_rowCode e _ _ head
          obtain ⟨remainder, perm, rfl⟩ := matchBag_rows tail
          refine ⟨remainder, ?_, ?_⟩
          · rw [List.map_cons, List.cons_append, ← found]
            exact (perm.cons _).trans (List.getElem_cons_eraseIdx_perm bound)
          · rw [mergeBindings_single] at merged
            exact (Option.some.inj merged).symm

/-- **A rule's rows match a store that begins with them**, the rest capturing the remainder. -/
theorem matchBag_prefix_rows (rest : String) (remainder : List Pattern) : ∀ rows : List Expr,
    MatchBagRel (rows.map rowCode) (some rest) .hashBag (rows.map rowCode ++ remainder)
      [(rest, .collection .hashBag remainder none)]
  | [] => .nilRest
  | e :: rows => by
      rw [List.map_cons]
      exact .cons 0 (by simp) (matchRel_self_rowCode e) (matchBag_prefix_rows rest remainder rows) rfl

/-- The right side of a rule, with the rest bound to a remainder, is the store of its rows and the
remainder. -/
theorem applyBindings_besideRest (rows : List Expr) (remainder : List Pattern) :
    applyBindings [("rest", .collection .hashBag remainder none)] (besideRest rows) =
      .collection .hashBag (rows.map rowCode ++ remainder) none := by
  rw [besideRest, applyBindings_collection]
  simp [restResolution, List.map_map, Function.comp_def, applyBindings_rowCode]

/-! ## The primitive step on stores -/

variable {relEnv : RelationEnv}

/-- **A primitive step from a store is a rule whose consumed rows are part of the store**, to the store with
them replaced by its yielded rows. -/
theorem step_storeCode {rows : List Expr} {target : Pattern}
    (step : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentWith R rules)
      (storeCode rows) target) :
    ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : List Expr,
      (R.consumed r ++ rest).Perm rows ∧ target = storeCode (R.yielded r ++ rest) := by
  obtain ⟨rule, member, bindings, matched, rfl⟩ := (step_iff_exists_match presentWith_plain).mp step
  obtain ⟨r, inRules, holds, index, rfl⟩ := of_mem_rewrites member
  rw [matchPattern_iff_matchRel] at matched
  change MatchRel (.collection .hashBag ((R.consumed r).map rowCode) (some "rest"))
    (.collection .hashBag (rows.map rowCode) none) bindings at matched
  cases matched with
  | collection _ bagMatch =>
      obtain ⟨remainder, perm, rfl⟩ := matchBag_rows bagMatch
      have each : ∀ p ∈ remainder, ∃ e, p = rowCode e := by
        intro p member
        obtain ⟨e, -, same⟩ := List.mem_map.mp (perm.subset (List.mem_append_right _ member))
        exact ⟨e, same.symm⟩
      obtain ⟨rest, rfl⟩ := exists_rows each
      refine ⟨r, inRules, holds, rest, ?_, ?_⟩
      · rw [← List.map_append] at perm
        exact (List.map_perm_map_iff rowCode_injective).mp perm
      · change applyBindings _ (besideRest (R.yielded r)) = _
        rw [applyBindings_besideRest, storeCode, List.map_append]

/-- **A rule steps a store that begins with what it consumes** to the store of what it yields beside the
rest. -/
theorem step_prefix {r : Rule Rows} (member : r ∈ rules) (holds : guardsHold r = true) (rest : List Expr) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentWith R rules)
      (storeCode (R.consumed r ++ rest)) (storeCode (R.yielded r ++ rest)) := by
  obtain ⟨index, presented⟩ := exists_mem_rewrites (R := R) member holds
  refine (step_iff_exists_match presentWith_plain).mpr ⟨namedRewrite R index r, presented,
    [("rest", .collection .hashBag (rest.map rowCode) none)], ?_, ?_⟩
  · rw [matchPattern_iff_matchRel]
    change MatchRel (.collection .hashBag ((R.consumed r).map rowCode) (some "rest"))
      (.collection .hashBag ((R.consumed r ++ rest).map rowCode) none) _
    rw [List.map_append]
    exact .collection (by decide) (matchBag_prefix_rows _ _ _)
  · change applyBindings _ (besideRest (R.yielded r)) = _
    rw [applyBindings_besideRest, storeCode, List.map_append]

/-! ## The framework's step and possibility on stores -/

/-- **The framework's step modulo equations from a store**: a rule whose consumed rows are part of the store,
to a term equal, modulo the equations, to the store with them replaced by its yielded rows. -/
theorem semanticStep_storeCode_iff {rows : List Expr} {target : Pattern} :
    langSemanticReducesUsing relEnv (presentWith R rules) (storeCode rows) target ↔
      ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : List Expr, (R.consumed r ++ rest).Perm rows ∧
        EquationEquiv (engineBasePremises relEnv) (presentWith R rules) (storeCode (R.yielded r ++ rest))
          target := by
  change StepModuloEquations (engineBasePremises relEnv) (presentWith R rules) (storeCode rows) target ↔ _
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_equationEquiv presentWith_equations presentWith_noAlgebra before
    obtain ⟨r, member, holds, rest, split, rfl⟩ := step_storeCode step
    exact ⟨r, member, holds, rest, split.trans perm.symm, after⟩
  · rintro ⟨r, member, holds, rest, split, after⟩
    exact ⟨storeCode (R.consumed r ++ rest), storeCode (R.yielded r ++ rest),
      equationEquiv_storeCode_of_perm presentWith_formers presentWith_store split.symm,
      step_prefix member holds rest, after⟩

/-- **The framework's generated possibility at a store**: some rule whose consumed rows are part of the store
leads to a store, of its yielded rows beside the rest, with the property. -/
theorem diamond_storeCode_iff (φ : EquationPredicate (langGSLTUsing relEnv (presentWith R rules)))
    (rows : List Expr) :
    (langDiamondUsing relEnv (presentWith R rules) φ).1 (storeCode rows) ↔
      ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : List Expr, (R.consumed r ++ rest).Perm rows ∧
        φ.1 (storeCode (R.yielded r ++ rest)) := by
  refine (langDiamondUsing_spec relEnv (presentWith R rules) φ (storeCode rows)).trans ?_
  constructor
  · rintro ⟨target, step, holds⟩
    obtain ⟨r, member, guards, rest, split, after⟩ := semanticStep_storeCode_iff.mp step
    exact ⟨r, member, guards, rest, split, (φ.2 after).mpr holds⟩
  · rintro ⟨r, member, guards, rest, split, holds⟩
    exact ⟨_, semanticStep_storeCode_iff.mpr ⟨r, member, guards, rest, split, Relation.EqvGen.refl _⟩, holds⟩

/-- **The parallel context rule holds**: a step of a store is a step of the store beside further rows. -/
theorem semanticStep_beside {rows next : List Expr} (extra : List Expr)
    (step : langSemanticReducesUsing relEnv (presentWith R rules) (storeCode rows) (storeCode next)) :
    langSemanticReducesUsing relEnv (presentWith R rules) (storeCode (rows ++ extra))
      (storeCode (next ++ extra)) := by
  obtain ⟨r, member, holds, rest, split, after⟩ := semanticStep_storeCode_iff.mp step
  have reached := (equationEquiv_storeCode_iff presentWith_equations presentWith_noAlgebra presentWith_formers
    presentWith_store).mp after
  refine semanticStep_storeCode_iff.mpr ⟨r, member, holds, rest ++ extra, ?_, ?_⟩
  · rw [← List.append_assoc]
    exact split.append_right extra
  · rw [← List.append_assoc]
    exact equationEquiv_storeCode_of_perm presentWith_formers presentWith_store (reached.append_right extra)

#print axioms presentWith_plain
#print axioms matchBag_rows
#print axioms step_storeCode
#print axioms step_prefix
#print axioms semanticStep_storeCode_iff
#print axioms diamond_storeCode_iff
#print axioms semanticStep_beside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
