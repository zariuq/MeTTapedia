import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.StructuralCodes
import Mettapedia.OSLF.MeTTaIL.UnaryNumeralMatching
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Rows and stores as terms of a presented language

The ground first-order step of the tree labels its rows by `NamesOnTheStep.Expr` (constants, application,
generative names, codes). This module presents those rows as the terms of a sort of a language
definition, and stores as bags of them.

* **The row formers** (`rowFormers`): one constructor of the sort `Row` per former of `Expr` (`Sym`, `App`,
  `Name`, `Code`), over numerals of a sort `Nat` (`Zero`, `Succ`, the tree's unary numerals). A row is coded
  by its formers (`rowCode`, injective: `rowCode_injective`), and every code has the sort `Row` in every
  language that declares these formers (`rowCode_typed`).
* **The union of stores** (`storeFormer`): a bag constructor of the sort `Store` whose one parameter is a bag
  of rows. A store of rows is the bag of their codes (`storeCode`).
* **Codes are rigid**: a code is matched only by itself and binds nothing (`rigid_rowCode`), it is its own
  canonical form (`canon_rowCode`), and the only term with its canonical form is itself (`eq_of_same_rowCode`).
* **Two stores are equal modulo the equations exactly when their rows are permutations**, in every language
  that declares these formers, has no authored equation and no collection algebra: permutations are the
  derived bag law (`equationEquiv_storeCode_of_perm`), and every equivalent term is the store of a
  permutation (`storeCode_of_equationEquiv`), since without authored equations and algebra every generator
  is a permutation (`bagSteps_of_equationEquiv`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.CanonicalBags
  (canon Same BagStep canon_apply canon_collection arrange_bag perm_of_sortLex_eq same_apply same_collection
    eqvGen_canon_eq)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.WellSorted
  (HasType ArgumentsHaveTypes ElementsHaveType FreeTypeContext UsesBareCollection CollectionTypedAt
    CollectionTypeOccurs)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (EquationEquiv EquationContextStep EquationGenerator DerivedInstance derivedInstance_equivalent
    no_equationInstance_of_equations_eq_nil no_algebraRule_of_hasAlgebraDeclarations_eq_false)
open NamesOnTheStep (Expr)

/-! ## The row signature -/

/-- **A row as a term of the sort `Row`**: one constructor per former of `Expr`, over unary numerals. -/
def rowCode : Expr → Pattern
  | .sym k => .apply "Sym" [Pattern.unary "Zero" "Succ" k]
  | .app f a => .apply "App" [rowCode f, rowCode a]
  | .name n => .apply "Name" [Pattern.unary "Zero" "Succ" n]
  | .code e => .apply "Code" [rowCode e]

theorem numeral_injective : Function.Injective (Pattern.unary "Zero" "Succ") :=
  Pattern.unary_injective (by decide)

/-- **The code of rows is injective.** -/
theorem rowCode_injective : Function.Injective rowCode := by
  intro first
  induction first with
  | sym k =>
      intro second same
      cases second with
      | sym _ => exact congrArg Expr.sym (numeral_injective (List.cons.inj (Pattern.apply.inj same).2).1)
      | app _ _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | name _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | code _ => exact absurd (Pattern.apply.inj same).1 (by decide)
  | app f a ihf iha =>
      intro second same
      cases second with
      | sym _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | app _ _ =>
          have args := List.cons.inj (Pattern.apply.inj same).2
          rw [ihf args.1, iha (List.cons.inj args.2).1]
      | name _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | code _ => exact absurd (Pattern.apply.inj same).1 (by decide)
  | name n =>
      intro second same
      cases second with
      | sym _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | app _ _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | name _ => exact congrArg Expr.name (numeral_injective (List.cons.inj (Pattern.apply.inj same).2).1)
      | code _ => exact absurd (Pattern.apply.inj same).1 (by decide)
  | code e ih =>
      intro second same
      cases second with
      | sym _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | app _ _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | name _ => exact absurd (Pattern.apply.inj same).1 (by decide)
      | code _ => exact congrArg Expr.code (ih (List.cons.inj (Pattern.apply.inj same).2).1)

/-! ## The grammar -/

/-- The numeral zero. -/
def zeroFormer : GrammarRule :=
  { label := "Zero", category := "Nat", params := [], syntaxPattern := [.terminal "0"] }

/-- The successor of a numeral. -/
def succFormer : GrammarRule :=
  { label := "Succ", category := "Nat", params := [.simple "n" (.base "Nat")],
    syntaxPattern := [.terminal "S", .nonTerminal "n"] }

/-- A constant row. -/
def symFormer : GrammarRule :=
  { label := "Sym", category := "Row", params := [.simple "k" (.base "Nat")],
    syntaxPattern := [.terminal "sym", .nonTerminal "k"] }

/-- An application row. -/
def appFormer : GrammarRule :=
  { label := "App", category := "Row", params := [.simple "f" (.base "Row"), .simple "a" (.base "Row")],
    syntaxPattern := [.terminal "(", .nonTerminal "f", .nonTerminal "a", .terminal ")"] }

/-- A generative name. -/
def nameFormer : GrammarRule :=
  { label := "Name", category := "Row", params := [.simple "n" (.base "Nat")],
    syntaxPattern := [.terminal "name", .nonTerminal "n"] }

/-- The code of a row. -/
def codeFormer : GrammarRule :=
  { label := "Code", category := "Row", params := [.simple "e" (.base "Row")],
    syntaxPattern := [.terminal "code", .nonTerminal "e"] }

/-- **The row formers**: the constructors of rows and of their numerals. -/
def rowFormers : List GrammarRule := [zeroFormer, succFormer, symFormer, appFormer, nameFormer, codeFormer]

/-- **The union of stores**: a bag of rows, of the sort `Store`. -/
def storeFormer : GrammarRule :=
  { label := "Store", category := "Store", params := [.simple "rows" (.bag (.base "Row"))],
    syntaxPattern := [.terminal "{", .nonTerminal "rows", .separator ",", .terminal "}"] }

/-! ## Rows have the sort `Row` -/

section Typing

variable {L : LanguageDef} (formersIn : rowFormers ⊆ L.terms) (free : FreeTypeContext) (bound : List TypeExpr)

theorem not_bare_of_simple {rule : GrammarRule} {name : String} {sort : String} {rest : List TermParam}
    (params : rule.params = .simple name (.base sort) :: rest) : ¬ UsesBareCollection rule := by
  rintro ⟨_, _, _, shape⟩
  obtain ⟨-, params'⟩ := (GrammarRule.bareParams_cons_iff rule _ []).mp shape
  rw [params] at params'
  cases params'

theorem zero_not_bare : ¬ UsesBareCollection zeroFormer := by
  rintro ⟨_, _, _, shape⟩
  cases shape

include formersIn in
/-- Every numeral has the sort `Nat`. -/
theorem numeral_typed : ∀ k : ℕ, HasType L free bound (Pattern.unary "Zero" "Succ" k) (.base "Nat")
  | 0 => .constructor (formersIn (List.Mem.head _)) zero_not_bare .nil
  | k + 1 => .constructor (formersIn (.tail _ (.head _))) (not_bare_of_simple rfl)
      (.cons trivial rfl (numeral_typed k) .nil)

include formersIn in
/-- **Every row has the sort `Row`.** -/
theorem rowCode_typed : ∀ e : Expr, HasType L free bound (rowCode e) (.base "Row")
  | .sym k => .constructor (formersIn (.tail _ (.tail _ (.head _)))) (not_bare_of_simple rfl)
      (.cons trivial rfl (numeral_typed formersIn free bound k) .nil)
  | .app f a => .constructor (formersIn (.tail _ (.tail _ (.tail _ (.head _))))) (not_bare_of_simple rfl)
      (.cons trivial rfl (rowCode_typed f) (.cons trivial rfl (rowCode_typed a) .nil))
  | .name n => .constructor (formersIn (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (not_bare_of_simple rfl)
      (.cons trivial rfl (numeral_typed formersIn free bound n) .nil)
  | .code e => .constructor (formersIn (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
      (not_bare_of_simple rfl) (.cons trivial rfl (rowCode_typed e) .nil)

include formersIn in
theorem rows_typed : ∀ rows : List Expr, ElementsHaveType L free bound (rows.map rowCode) (.base "Row")
  | [] => .nil _ _
  | e :: rows => .cons (rowCode_typed formersIn free bound e) (rows_typed rows)

end Typing

/-! ## Codes are rigid -/

/-- **A rigid pattern**: matched only by itself, binding nothing. -/
def Rigid (p : Pattern) : Prop := ∀ t bindings, MatchRel p t bindings → t = p ∧ bindings = []

theorem mergeBindings_nil_nil : mergeBindings [] [] = some [] := rfl

theorem rigid_args : ∀ {ps : List Pattern}, (∀ p ∈ ps, Rigid p) →
    ∀ {ts : List Pattern} {bindings : Bindings}, MatchArgsRel ps ts bindings → ts = ps ∧ bindings = []
  | [], _, _, _, matched => by
      cases matched
      exact ⟨rfl, rfl⟩
  | p :: _, rigid, _, _, matched => by
      cases matched with
      | cons head tail merged =>
          obtain ⟨rfl, rfl⟩ := rigid p List.mem_cons_self _ _ head
          obtain ⟨rfl, rfl⟩ := rigid_args (fun q member => rigid q (List.mem_cons_of_mem _ member)) tail
          rw [mergeBindings_nil_nil] at merged
          exact ⟨rfl, (Option.some.inj merged).symm⟩

theorem rigid_apply {c : String} {args : List Pattern} (rigid : ∀ p ∈ args, Rigid p) : Rigid (.apply c args) := by
  intro t bindings matched
  cases matched with
  | apply argsMatched _ =>
      obtain ⟨rfl, rfl⟩ := rigid_args rigid argsMatched
      exact ⟨rfl, rfl⟩

theorem rigid_numeral : ∀ k : ℕ, Rigid (Pattern.unary "Zero" "Succ" k)
  | 0 => rigid_apply fun _ member => absurd member List.not_mem_nil
  | k + 1 => rigid_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact rigid_numeral k

/-- **A row is matched only by itself, binding nothing.** -/
theorem rigid_rowCode : ∀ e : Expr, Rigid (rowCode e)
  | .sym k => rigid_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact rigid_numeral k
  | .app f a => rigid_apply fun p member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact rigid_rowCode f
      · rw [List.mem_singleton.mp member]
        exact rigid_rowCode a
  | .name n => rigid_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact rigid_numeral n
  | .code e => rigid_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact rigid_rowCode e

theorem matchArgs_self : ∀ {ps : List Pattern}, (∀ p ∈ ps, MatchRel p p []) → MatchArgsRel ps ps []
  | [], _ => .nil
  | p :: _, self => .cons (self p List.mem_cons_self)
      (matchArgs_self fun q member => self q (List.mem_cons_of_mem p member)) mergeBindings_nil_nil

theorem matchRel_self_apply {c : String} {args : List Pattern} (self : ∀ p ∈ args, MatchRel p p []) :
    MatchRel (.apply c args) (.apply c args) [] :=
  .apply (matchArgs_self self) rfl

theorem matchRel_self_numeral : ∀ k : ℕ, MatchRel (Pattern.unary "Zero" "Succ" k) (Pattern.unary "Zero" "Succ" k) []
  | 0 => matchRel_self_apply fun _ member => absurd member List.not_mem_nil
  | k + 1 => matchRel_self_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact matchRel_self_numeral k

/-- **A row matches itself, binding nothing.** -/
theorem matchRel_self_rowCode : ∀ e : Expr, MatchRel (rowCode e) (rowCode e) []
  | .sym k => matchRel_self_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact matchRel_self_numeral k
  | .app f a => matchRel_self_apply fun p member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact matchRel_self_rowCode f
      · rw [List.mem_singleton.mp member]
        exact matchRel_self_rowCode a
  | .name n => matchRel_self_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact matchRel_self_numeral n
  | .code e => matchRel_self_apply fun p member => by
      rw [List.mem_singleton.mp member]
      exact matchRel_self_rowCode e

/-- An instantiation leaves a row unchanged. -/
theorem applyBindings_rowCode (bindings : Bindings) : ∀ e : Expr, applyBindings bindings (rowCode e) = rowCode e
  | .sym k => by simp [rowCode, applyBindings]
  | .app f a => by simp [rowCode, applyBindings, applyBindings_rowCode bindings f, applyBindings_rowCode bindings a]
  | .name n => by simp [rowCode, applyBindings]
  | .code e => by simp [rowCode, applyBindings, applyBindings_rowCode bindings e]

/-- A row binds nothing. -/
theorem binderFree_rowCode : ∀ e : Expr, binderFree (rowCode e) = true
  | .sym k => by simp [rowCode, binderFree, binderFreeList]
  | .app f a => by simp [rowCode, binderFree, binderFreeList, binderFree_rowCode f, binderFree_rowCode a]
  | .name n => by simp [rowCode, binderFree, binderFreeList]
  | .code e => by simp [rowCode, binderFree, binderFreeList, binderFree_rowCode e]

theorem binderFreeList_rows : ∀ rows : List Expr, binderFreeList (rows.map rowCode) = true
  | [] => rfl
  | e :: rows => by simp only [List.map_cons, binderFreeList, binderFree_rowCode e, binderFreeList_rows rows,
      Bool.and_self]

/-! ## Codes are canonical, and nothing else has their canonical form -/

theorem canon_numeral : ∀ k : ℕ, canon (Pattern.unary "Zero" "Succ" k) = Pattern.unary "Zero" "Succ" k
  | 0 => by rw [Pattern.unary_zero, canon_apply, List.map_nil]
  | k + 1 => by rw [Pattern.unary_succ, canon_apply, List.map_cons, List.map_nil, canon_numeral k]

/-- **A row is its own canonical form.** -/
theorem canon_rowCode : ∀ e : Expr, canon (rowCode e) = rowCode e
  | .sym k => by rw [rowCode, canon_apply, List.map_cons, List.map_nil, canon_numeral]
  | .app f a => by rw [rowCode, canon_apply, List.map_cons, List.map_cons, List.map_nil, canon_rowCode f,
      canon_rowCode a]
  | .name n => by rw [rowCode, canon_apply, List.map_cons, List.map_nil, canon_numeral]
  | .code e => by rw [rowCode, canon_apply, List.map_cons, List.map_nil, canon_rowCode e]

theorem eq_of_map_canon : ∀ {as others : List Pattern}, (∀ a ∈ as, ∀ o, Same a o → o = a) →
    as.map canon = others.map canon → others = as
  | [], [], _, _ => rfl
  | [], _ :: _, _, same => by simp at same
  | _ :: _, [], _, same => by simp at same
  | a :: _, o :: _, rigid, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      rw [rigid a List.mem_cons_self o same.1,
        eq_of_map_canon (fun b member => rigid b (List.mem_cons_of_mem a member)) same.2]

theorem eq_of_same_apply {c : String} {args : List Pattern} (rigid : ∀ a ∈ args, ∀ o, Same a o → o = a)
    {p : Pattern} (same : Same (.apply c args) p) : p = .apply c args := by
  obtain ⟨others, rfl, mapped⟩ := same_apply same
  rw [eq_of_map_canon rigid mapped]

theorem eq_of_same_numeral : ∀ (k : ℕ) (p : Pattern), Same (Pattern.unary "Zero" "Succ" k) p →
    p = Pattern.unary "Zero" "Succ" k
  | 0, _, same => eq_of_same_apply (fun _ member => absurd member List.not_mem_nil) same
  | k + 1, _, same => eq_of_same_apply (fun a member => by
      rw [List.mem_singleton.mp member]
      exact eq_of_same_numeral k) same

/-- **The only term with a row's canonical form is the row.** -/
theorem eq_of_same_rowCode : ∀ (e : Expr) (p : Pattern), Same (rowCode e) p → p = rowCode e
  | .sym k, _, same => eq_of_same_apply (fun a member => by
      rw [List.mem_singleton.mp member]
      exact eq_of_same_numeral k) same
  | .app f a, _, same => eq_of_same_apply (fun b member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact eq_of_same_rowCode f
      · rw [List.mem_singleton.mp member]
        exact eq_of_same_rowCode a) same
  | .name n, _, same => eq_of_same_apply (fun a member => by
      rw [List.mem_singleton.mp member]
      exact eq_of_same_numeral n) same
  | .code e, _, same => eq_of_same_apply (fun a member => by
      rw [List.mem_singleton.mp member]
      exact eq_of_same_rowCode e) same

/-! ## Stores -/

/-- **A store of rows**: the bag of their codes. -/
def storeCode (rows : List Expr) : Pattern := .collection .hashBag (rows.map rowCode) none

theorem storeCode_injective : Function.Injective storeCode := by
  intro first second same
  simp only [storeCode, Pattern.collection.injEq, true_and, and_true] at same
  exact (List.map_injective_iff.mpr rowCode_injective) same

/-- A list of patterns each of which is a row is the list of codes of some rows. -/
theorem exists_rows : ∀ {patterns : List Pattern}, (∀ p ∈ patterns, ∃ e, p = rowCode e) →
    ∃ rows : List Expr, patterns = rows.map rowCode
  | [], _ => ⟨[], rfl⟩
  | p :: _, each => by
      obtain ⟨e, rfl⟩ := each p List.mem_cons_self
      obtain ⟨rows, rfl⟩ := exists_rows fun q member => each q (List.mem_cons_of_mem _ member)
      exact ⟨e :: rows, rfl⟩

/-- **A term with a store's canonical form is the store of a permutation of its rows.** -/
theorem storeCode_of_same {rows : List Expr} {q : Pattern} (same : Same (storeCode rows) q) :
    ∃ others : List Expr, q = storeCode others ∧ rows.Perm others := by
  obtain ⟨elements, rfl, arranged⟩ := same_collection same
  rw [arrange_bag, arrange_bag] at arranged
  have perm := perm_of_sortLex_eq arranged
  have canonical : (rows.map rowCode).map canon = rows.map rowCode := by
    rw [List.map_map]
    exact List.map_congr_left fun e _ => canon_rowCode e
  rw [canonical] at perm
  have each : ∀ p ∈ elements, ∃ e, p = rowCode e := by
    intro p member
    obtain ⟨e, -, same⟩ := List.mem_map.mp (perm.symm.subset (List.mem_map_of_mem (f := canon) member))
    exact ⟨e, eq_of_same_rowCode e p ((canon_rowCode e).trans same)⟩
  obtain ⟨others, rfl⟩ := exists_rows each
  have back : (others.map rowCode).map canon = others.map rowCode := by
    rw [List.map_map]
    exact List.map_congr_left fun e _ => canon_rowCode e
  rw [back] at perm
  exact ⟨others, rfl, (List.map_perm_map_iff rowCode_injective).mp perm⟩

/-! ## Equations of stores -/

section Equations

variable {base : BasePremiseEvaluator} {L : LanguageDef}

/-- Without authored equations and collection algebra, every generator of the equations is a permutation of an
unordered collection. -/
theorem bagStep_of_generator (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    {p q : Pattern} (generator : EquationGenerator base L p q) : BagStep p q := by
  rcases generator with authored | derived
  · exact absurd authored (no_equationInstance_of_equations_eq_nil noEquations p q)
  · cases derived with
    | bagPerm _ _ permutation => exact .permute rfl permutation
    | setPerm _ _ permutation => exact .permute rfl permutation
    | setDedup _ _ => exact .members fun a => by simp
    | flatten declared _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declared).elim
    | singleton declared _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declared).elim
    | unitElim declared _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declared).elim
    | emptyUnit declared _ _ => exact (no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra declared).elim

/-- **Without authored equations and collection algebra, the equations are generated by permutations.** -/
theorem bagSteps_of_equationEquiv (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    {p q : Pattern} (equivalent : EquationEquiv base L p q) : Relation.EqvGen BagStep p q :=
  Relation.EqvGen.mono (fun _ _ step => by
    cases step with
    | inContext context generator => exact BagStep.fill context (bagStep_of_generator noEquations noAlgebra generator))
    _ _ equivalent

/-- **A term equal to a store modulo the equations is the store of a permutation of its rows.** -/
theorem storeCode_of_equationEquiv (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    {rows : List Expr} {q : Pattern} (equivalent : EquationEquiv base L (storeCode rows) q) :
    ∃ others : List Expr, q = storeCode others ∧ rows.Perm others :=
  storeCode_of_same (eqvGen_canon_eq (bagSteps_of_equationEquiv noEquations noAlgebra equivalent))

/-- The rows of a store are a bag at the store former. -/
theorem collectionTyped (formersIn : rowFormers ⊆ L.terms) (rows : List Expr) :
    CollectionTypedAt L storeFormer .hashBag (rows.map rowCode) :=
  ⟨.simple "rows" (.bag (.base "Row")), List.mem_singleton_self _, .base "Row", .here, FreeTypeContext.empty, [],
    .collection (rows_typed formersIn FreeTypeContext.empty [] rows)⟩

/-- **A permutation of a store's rows is an equation**, by the derived bag law. -/
theorem equationEquiv_storeCode_of_perm (formersIn : rowFormers ⊆ L.terms) (storeIn : storeFormer ∈ L.terms)
    {rows others : List Expr} (perm : rows.Perm others) : EquationEquiv base L (storeCode rows) (storeCode others) :=
  derivedInstance_equivalent (DerivedInstance.bagPerm storeIn (collectionTyped formersIn rows) (perm.map rowCode))

/-- **Two stores are equal modulo the equations exactly when their rows are permutations.** -/
theorem equationEquiv_storeCode_iff (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    (formersIn : rowFormers ⊆ L.terms) (storeIn : storeFormer ∈ L.terms) {rows others : List Expr} :
    EquationEquiv base L (storeCode rows) (storeCode others) ↔ rows.Perm others := by
  constructor
  · intro equivalent
    obtain ⟨found, same, perm⟩ := storeCode_of_equationEquiv noEquations noAlgebra equivalent
    rw [storeCode_injective same]
    exact perm
  · exact equationEquiv_storeCode_of_perm formersIn storeIn

end Equations

#print axioms rowCode_injective
#print axioms rowCode_typed
#print axioms rigid_rowCode
#print axioms matchRel_self_rowCode
#print axioms applyBindings_rowCode
#print axioms canon_rowCode
#print axioms eq_of_same_rowCode
#print axioms storeCode_of_same
#print axioms bagSteps_of_equationEquiv
#print axioms storeCode_of_equationEquiv
#print axioms equationEquiv_storeCode_of_perm
#print axioms equationEquiv_storeCode_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
