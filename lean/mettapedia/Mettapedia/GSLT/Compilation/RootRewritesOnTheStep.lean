import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mettapedia.OSLF.Framework.RuleInstanceSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting
import Mettapedia.Languages.TransitionSystem.LanguageDef

/-!
# Authored root rewrites compiled to the transform step

A language whose rewrites are premise-free, first-order and bind every variable
of their result is compiled to one transform rule per authored rewrite, in the
authored order (`compile`, `compile_origins`). A source term is one row.

* **Source semantics**: the language's own syntactic one-step reduction
  (`ContextualStep.Step`). It is neither defined by the compiled program nor
  read modulo derived collection laws.
* **Exactness**: a source reduction is a root rewrite of the encoded row, and a
  root rewrite of an encoded row is a source reduction (`rootStep_encode_iff`,
  `rootStep_image`).
* **On the step**: one reduction for one firing, in both directions
  (`stepCorrespondence`, by `Machines.rootCorrespondence`).
* **Text**: the program in tcalc notation, one `take`/`make` rule per rewrite
  (`programText`). No theorem here speaks about a reader of that text.
* **Observation**: which successors are possible. Neither the order nor the
  multiplicity of equal successors is observed.
* **Refusals**: equations, algebra declarations, premises, rewrites under
  binders, collection patterns and unbound result variables. A refusal names
  the rule. The source keeps its meaning (`Controls.literal_source_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.RootRewritesOnTheStep

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode collectionCode_injective)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines

/-! ## Labels

`PatternCode.stringCode` nests pairings, so its size is exponential in the length
of a label. A positional code is linear. -/

/-- The positional code of a list of characters. -/
def charsCode : List Char → Nat
  | [] => 0
  | char :: chars => char.toNat + 1 + 1114113 * charsCode chars

theorem char_toNat_lt (char : Char) : char.toNat < 1114112 := by
  rcases char.valid with below | ⟨_, below⟩
  · exact Nat.lt_trans below (by decide)
  · exact below

theorem charsCode_injective : Function.Injective charsCode := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons _ _ => simp only [charsCode] at same; omega
  | cons char chars ih =>
      intro right same
      cases right with
      | nil => simp only [charsCode] at same; omega
      | cons other others =>
          simp only [charsCode] at same
          have first := char_toNat_lt char
          have second := char_toNat_lt other
          have heads : char.toNat = other.toNat := by omega
          have tails : charsCode chars = charsCode others := by omega
          rw [Char.toNat_inj.mp heads, ih tails]

/-- The code of a label or a variable name. -/
def labelCode (label : String) : Nat := charsCode label.toList

theorem labelCode_injective : Function.Injective labelCode := fun _ _ same =>
  String.toList_inj.mp (charsCode_injective same)

/-! ## A term as a row -/

/-- An optional name as a row. -/
def optionRow : Option String → Expr
  | none => .sym 0
  | some name => .code (.sym (labelCode name))

/-- A list of names as a row. -/
def namesRow : List String → Expr
  | [] => .sym 0
  | name :: names => .app (.sym (labelCode name)) (namesRow names)

mutual
  /-- **A source term as one row.** Every term has a row, also a term that a rule
  can only capture whole. -/
  def encode : Pattern → Expr
    | .bvar index => .app (.sym 0) (.sym index)
    | .fvar name => .app (.sym 1) (.sym (labelCode name))
    | .apply label arguments => .app (.sym 2) (.app (.sym (labelCode label)) (encodeList arguments))
    | .lambda binder body => .app (.sym 3) (.app (optionRow binder) (encode body))
    | .multiLambda arity binders body =>
        .app (.sym 4) (.app (.sym arity) (.app (namesRow binders) (encode body)))
    | .subst body value => .app (.sym 5) (.app (encode body) (encode value))
    | .collection kind elements rest =>
        .app (.sym 6) (.app (.sym (collectionCode kind)) (.app (encodeList elements) (optionRow rest)))

  /-- A list of source terms as one row. -/
  def encodeList : List Pattern → Expr
    | [] => .sym 0
    | term :: terms => .app (encode term) (encodeList terms)
end

theorem optionRow_injective : Function.Injective optionRow := by
  intro left right same
  cases left <;> cases right <;> simp_all [optionRow, labelCode_injective.eq_iff]

theorem namesRow_injective : Function.Injective namesRow := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [namesRow]
  | cons name names ih =>
      intro right same
      cases right with
      | nil => simp [namesRow] at same
      | cons other others =>
          simp only [namesRow, Expr.app.injEq, Expr.sym.injEq] at same
          rw [labelCode_injective same.1, ih same.2]

mutual
  theorem encode_inj : ∀ (left right : Pattern), encode left = encode right → left = right
    | .bvar _, right, same => by cases right <;> simp_all [encode]
    | .fvar _, right, same => by cases right <;> simp_all [encode, labelCode_injective.eq_iff]
    | .apply _ arguments, right, same => by
        cases right <;> simp [encode] at same
        rw [labelCode_injective same.1, encodeList_inj arguments _ same.2]
    | .lambda _ body, right, same => by
        cases right <;> simp [encode] at same
        rw [optionRow_injective same.1, encode_inj body _ same.2]
    | .multiLambda _ _ body, right, same => by
        cases right <;> simp [encode] at same
        rw [same.1, namesRow_injective same.2.1, encode_inj body _ same.2.2]
    | .subst body value, right, same => by
        cases right <;> simp [encode] at same
        rw [encode_inj body _ same.1, encode_inj value _ same.2]
    | .collection _ elements _, right, same => by
        cases right <;> simp [encode] at same
        rw [collectionCode_injective same.1, encodeList_inj elements _ same.2.1,
          optionRow_injective same.2.2]

  theorem encodeList_inj : ∀ (left right : List Pattern), encodeList left = encodeList right → left = right
    | [], right, same => by cases right <;> simp_all [encodeList]
    | term :: terms, right, same => by
        cases right <;> simp [encodeList] at same
        rw [encode_inj term _ same.1, encodeList_inj terms _ same.2]
end

theorem encode_injective : Function.Injective encode := fun left right => encode_inj left right

/-! ## A first-order rule side as a row pattern -/

/-- An application of row patterns. -/
def appTerm (function argument : Tm) : Tm := .app RowFunction.app (args2 function argument)

/-- A constant row pattern. -/
def symTerm (code : Nat) : Tm := .const (.sym code)

@[simp] theorem inst_appTerm (θ : ℕ → Expr) (function argument : Tm) :
    inst θ (appTerm function argument) = .app (inst θ function) (inst θ argument) := rfl

@[simp] theorem inst_symTerm (θ : ℕ → Expr) (code : Nat) : inst θ (symTerm code) = .sym code := rfl

@[simp] theorem unknowns_appTerm (function argument : Tm) :
    unknowns (appTerm function argument) = unknowns function ++ unknowns argument := rfl

@[simp] theorem unknowns_symTerm (code : Nat) : unknowns (symTerm code) = [] := rfl

mutual
  /-- A first-order pattern as a row pattern. Binders, explicit substitutions and
  collection patterns have none. -/
  def lower? : Pattern → Option Tm
    | .fvar name => some (.var (labelCode name))
    | .bvar index => some (appTerm (symTerm 0) (symTerm index))
    | .apply label arguments =>
        (lowerList? arguments).map fun lowered => appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) lowered)
    | .lambda _ _ => none
    | .multiLambda _ _ _ => none
    | .subst _ _ => none
    | .collection _ _ _ => none

  /-- A list of first-order patterns as one row pattern. -/
  def lowerList? : List Pattern → Option Tm
    | [] => some (symTerm 0)
    | pattern :: patterns =>
        (lower? pattern).bind fun first => (lowerList? patterns).map fun others => appTerm first others
end

mutual
  /-- What lowers is matched exactly by the framework's matcher. -/
  theorem matchCorrect_of_lower : ∀ (pattern : Pattern) (term : Tm),
      lower? pattern = some term → isMatchCorrectAux pattern = true
    | .fvar _, _, _ => by simp [isMatchCorrectAux]
    | .bvar _, _, _ => by simp [isMatchCorrectAux]
    | .apply _ arguments, _, lowered => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨inner, innerLowered, _⟩ := lowered
        simpa [isMatchCorrectAux] using matchCorrectList_of_lower arguments inner innerLowered
    | .lambda _ _, _, lowered => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, lowered => by simp [lower?] at lowered
    | .subst _ _, _, lowered => by simp [lower?] at lowered
    | .collection _ _ _, _, lowered => by simp [lower?] at lowered

  theorem matchCorrectList_of_lower : ∀ (patterns : List Pattern) (term : Tm),
      lowerList? patterns = some term → isMatchCorrectListAux patterns = true
    | [], _, _ => by simp [isMatchCorrectListAux]
    | pattern :: patterns, _, lowered => by
        simp only [lowerList?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨first, firstLowered, others, othersLowered, _⟩ := lowered
        simp [isMatchCorrectListAux, matchCorrect_of_lower pattern first firstLowered,
          matchCorrectList_of_lower patterns others othersLowered]
end

mutual
  /-- The unknowns of a lowered pattern are the codes of its variables. -/
  theorem unknowns_lower : ∀ (pattern : Pattern) (term : Tm),
      lower? pattern = some term → unknowns term = (freeVars pattern).map labelCode
    | .fvar _, _, lowered => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        simp [unknowns, freeVars]
    | .bvar _, _, lowered => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        simp [freeVars]
    | .apply _ arguments, _, lowered => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨inner, innerLowered, rfl⟩ := lowered
        simp [freeVars, unknowns_lowerList arguments inner innerLowered]
    | .lambda _ _, _, lowered => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, lowered => by simp [lower?] at lowered
    | .subst _ _, _, lowered => by simp [lower?] at lowered
    | .collection _ _ _, _, lowered => by simp [lower?] at lowered

  theorem unknowns_lowerList : ∀ (patterns : List Pattern) (term : Tm),
      lowerList? patterns = some term → unknowns term = (patterns.flatMap freeVars).map labelCode
    | [], _, lowered => by
        simp only [lowerList?, Option.some.injEq] at lowered
        subst lowered
        simp
    | pattern :: patterns, _, lowered => by
        simp only [lowerList?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨first, firstLowered, others, othersLowered, rfl⟩ := lowered
        simp [unknowns_lower pattern first firstLowered, unknowns_lowerList patterns others othersLowered]
end

mutual
  /-- **Lowering commutes with substitution.** -/
  theorem inst_lower (θ : ℕ → Expr) (bindings : Bindings) : ∀ (pattern : Pattern) (term : Tm),
      lower? pattern = some term →
      (∀ name ∈ freeVars pattern, θ (labelCode name) = encode (applyBindings bindings (.fvar name))) →
      inst θ term = encode (applyBindings bindings pattern)
    | .fvar name, _, lowered, agree => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        exact agree name (by simp [freeVars])
    | .bvar _, _, lowered, _ => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        simp [applyBindings, encode]
    | .apply _ arguments, _, lowered, agree => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨inner, innerLowered, rfl⟩ := lowered
        have innerInst := inst_lowerList θ bindings arguments inner innerLowered
          (fun name member => agree name (by simpa [freeVars] using member))
        simp [applyBindings, encode, innerInst]
    | .lambda _ _, _, lowered, _ => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, lowered, _ => by simp [lower?] at lowered
    | .subst _ _, _, lowered, _ => by simp [lower?] at lowered
    | .collection _ _ _, _, lowered, _ => by simp [lower?] at lowered

  theorem inst_lowerList (θ : ℕ → Expr) (bindings : Bindings) : ∀ (patterns : List Pattern) (term : Tm),
      lowerList? patterns = some term →
      (∀ name ∈ patterns.flatMap freeVars, θ (labelCode name) = encode (applyBindings bindings (.fvar name))) →
      inst θ term = encodeList (patterns.map (applyBindings bindings))
    | [], _, lowered, _ => by
        simp only [lowerList?, Option.some.injEq] at lowered
        subst lowered
        simp [encodeList]
    | pattern :: patterns, _, lowered, agree => by
        simp only [lowerList?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨first, firstLowered, others, othersLowered, rfl⟩ := lowered
        simp only [List.flatMap_cons, List.mem_append] at agree
        simp [encodeList, inst_lower θ bindings pattern first firstLowered (fun name member => agree name (.inl member)),
          inst_lowerList θ bindings patterns others othersLowered (fun name member => agree name (.inr member))]
end

mutual
  /-- **A pattern captures source terms only.** Where a lowered pattern meets an
  encoded term, every unknown holds an encoded term. -/
  theorem captures (θ : ℕ → Expr) : ∀ (pattern : Pattern) (term : Tm) (source : Pattern),
      lower? pattern = some term → inst θ term = encode source →
      ∀ name ∈ freeVars pattern, ∃ value, θ (labelCode name) = encode value
    | .fvar _, _, source, lowered, met => by
        simp only [lower?, Option.some.injEq] at lowered
        subst lowered
        intro name member
        simp only [freeVars, List.mem_singleton] at member
        subst member
        exact ⟨source, met⟩
    | .bvar _, _, _, _, _ => by simp [freeVars]
    | .apply _ arguments, _, source, lowered, met => by
        simp only [lower?, Option.map_eq_some_iff] at lowered
        obtain ⟨inner, innerLowered, rfl⟩ := lowered
        cases source <;> simp [encode] at met
        intro name member
        exact capturesList θ arguments inner _ innerLowered met.2 name (by simpa [freeVars] using member)
    | .lambda _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .multiLambda _ _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .subst _ _, _, _, lowered, _ => by simp [lower?] at lowered
    | .collection _ _ _, _, _, lowered, _ => by simp [lower?] at lowered

  theorem capturesList (θ : ℕ → Expr) : ∀ (patterns : List Pattern) (term : Tm) (sources : List Pattern),
      lowerList? patterns = some term → inst θ term = encodeList sources →
      ∀ name ∈ patterns.flatMap freeVars, ∃ value, θ (labelCode name) = encode value
    | [], _, _, _, _ => by simp
    | pattern :: patterns, _, sources, lowered, met => by
        simp only [lowerList?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
        obtain ⟨first, firstLowered, others, othersLowered, rfl⟩ := lowered
        cases sources <;> simp [encodeList] at met
        intro name member
        simp only [List.flatMap_cons, List.mem_append] at member
        rcases member with inFirst | inOthers
        · exact captures θ pattern first _ firstLowered met.1 name inFirst
        · exact capturesList θ patterns others _ othersLowered met.2 name inOthers
end

/-- Finitely many captured terms are one list of bindings. -/
theorem exists_bindings (θ : ℕ → Expr) : ∀ (names : List String),
    (∀ name ∈ names, ∃ value, θ (labelCode name) = encode value) →
    ∃ bindings : Bindings, ∀ name ∈ names, θ (labelCode name) = encode (applyBindings bindings (.fvar name))
  | [], _ => ⟨[], by simp⟩
  | first :: others, captured => by
      obtain ⟨value, valued⟩ := captured first (by simp)
      obtain ⟨bindings, bound⟩ := exists_bindings θ others (fun name member => captured name (by simp [member]))
      refine ⟨(first, value) :: bindings, fun name member => ?_⟩
      by_cases same : first = name
      · subst same
        simpa [applyBindings] using valued
      · have later : name ∈ others := (List.mem_cons.mp member).resolve_left (fun equal => same equal.symm)
        simpa [applyBindings, List.find?_cons, same] using bound name later

/-! ## The compiler -/

/-- Why a language is not compiled by this lowering. -/
inductive Refusal where
  | staticEquations
  | premises (rule : String)
  | movedAcrossBinder (rule : String)
  | notFirstOrder (rule : String)
  | unboundInResult (rule : String)
  deriving DecidableEq, Repr

/-- The schema of one authored rewrite, or why it has none. -/
def lowerRule (rule : RewriteRule) : Except Refusal (Tm × Tm) :=
  if rule.premises.isEmpty then
    if ruleDepthAligned rule then
      match lower? rule.left, lower? rule.right with
      | some left, some right =>
          if (freeVars rule.right).all (fun name => (freeVars rule.left).contains name) then .ok (left, right)
          else .error (.unboundInResult rule.name)
      | _, _ => .error (.notFirstOrder rule.name)
    else .error (.movedAcrossBinder rule.name)
  else .error (.premises rule.name)

/-- The schemas of authored rewrites, in their order. -/
def lowerRules : List RewriteRule → Except Refusal (List (Tm × Tm))
  | [] => .ok []
  | rule :: rules =>
      match lowerRule rule with
      | .error reason => .error reason
      | .ok schema =>
          match lowerRules rules with
          | .error reason => .error reason
          | .ok schemas => .ok (schema :: schemas)

/-- **Compile an authored language to transform schemas.** `Machines.rootRules` reads
them as the program. -/
def compile (language : LanguageDef) : Except Refusal (List (Tm × Tm)) :=
  if language.equations.isEmpty && !language.hasAlgebraDeclarations then lowerRules language.rewrites
  else .error .staticEquations

/-- What a schema keeps of the rewrite it comes from. -/
structure Origin (rule : RewriteRule) (schema : Tm × Tm) : Prop where
  premiseFree : rule.premises = []
  aligned : ruleDepthAligned rule = true
  left : lower? rule.left = some schema.1
  right : lower? rule.right = some schema.2
  bound : ∀ name ∈ freeVars rule.right, name ∈ freeVars rule.left

theorem lowerRule_origin {rule : RewriteRule} {schema : Tm × Tm} (lowered : lowerRule rule = .ok schema) :
    Origin rule schema := by
  unfold lowerRule at lowered
  split at lowered
  · rename_i premiseFree
    split at lowered
    · rename_i aligned
      split at lowered
      · rename_i left right leftLowered rightLowered
        split at lowered
        · rename_i bound
          cases lowered
          exact ⟨List.isEmpty_iff.mp premiseFree, aligned, leftLowered, rightLowered,
            fun name member => List.contains_iff_mem.mp (List.all_eq_true.mp bound name member)⟩
        · cases lowered
      · cases lowered
    · cases lowered
  · cases lowered

theorem lowerRules_origins : ∀ {rules : List RewriteRule} {schemas : List (Tm × Tm)},
    lowerRules rules = .ok schemas → List.Forall₂ Origin rules schemas
  | [], _, lowered => by cases lowered; exact .nil
  | rule :: rules, _, lowered => by
      unfold lowerRules at lowered
      split at lowered
      · cases lowered
      · rename_i schema first
        split at lowered
        · cases lowered
        · rename_i schemas others
          cases lowered
          exact .cons (lowerRule_origin first) (lowerRules_origins others)

/-- **Coverage.** Every authored rewrite has its schema, in order, and no other schema exists. -/
theorem compile_origins {language : LanguageDef} {schemas : List (Tm × Tm)}
    (compiled : compile language = .ok schemas) : List.Forall₂ Origin language.rewrites schemas := by
  unfold compile at compiled
  split at compiled
  · exact lowerRules_origins compiled
  · cases compiled

theorem exists_schema {rules : List RewriteRule} {schemas : List (Tm × Tm)}
    (origins : List.Forall₂ Origin rules schemas) {rule : RewriteRule} (member : rule ∈ rules) :
    ∃ schema ∈ schemas, Origin rule schema := by
  induction origins with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨schema, schemaMember, origin⟩ := ih later
        exact ⟨schema, List.mem_cons_of_mem _ schemaMember, origin⟩

theorem exists_rule {rules : List RewriteRule} {schemas : List (Tm × Tm)}
    (origins : List.Forall₂ Origin rules schemas) {schema : Tm × Tm} (member : schema ∈ schemas) :
    ∃ rule ∈ rules, Origin rule schema := by
  induction origins with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨rule, ruleMember, origin⟩ := ih later
        exact ⟨rule, List.mem_cons_of_mem _ ruleMember, origin⟩

theorem compile_plain {language : LanguageDef} {schemas : List (Tm × Tm)}
    (compiled : compile language = .ok schemas) : PlainRules language := fun _ member => by
  obtain ⟨_, _, origin⟩ := exists_schema (compile_origins compiled) member
  exact ⟨origin.premiseFree, origin.aligned⟩

theorem compile_closed {language : LanguageDef} {schemas : List (Tm × Tm)}
    (compiled : compile language = .ok schemas) :
    ∀ schema ∈ schemas, ∀ x ∈ unknowns schema.2, x ∈ unknowns schema.1 := by
  intro schema member x inRight
  obtain ⟨rule, _, origin⟩ := exists_rule (compile_origins compiled) member
  rw [unknowns_lower _ _ origin.right] at inRight
  rw [unknowns_lower _ _ origin.left]
  obtain ⟨name, nameMember, rfl⟩ := List.mem_map.mp inRight
  exact List.mem_map.mpr ⟨name, origin.bound name nameMember, rfl⟩

/-! ## Exactness -/

variable {relEnv : RelationEnv} {language : LanguageDef} {schemas : List (Tm × Tm)}

/-- A source reduction is a root rewrite of the encoded row. -/
theorem rootStep_of_step (compiled : compile language = .ok schemas) {source target : Pattern}
    (stepped : Step (engineBasePremises relEnv) language source target) :
    RootStep schemas (encode source) (encode target) := by
  have origins := compile_origins compiled
  obtain ⟨rule, member, bindings, rfl, rfl⟩ := sides_of_step (compile_plain compiled)
    (fun rule member => by
      obtain ⟨schema, _, origin⟩ := exists_schema origins member
      exact matchCorrect_of_lower _ _ origin.left) stepped
  obtain ⟨schema, schemaMember, origin⟩ := exists_schema origins member
  let θ : ℕ → Expr :=
    Function.extend labelCode (fun name => encode (applyBindings bindings (.fvar name))) (fun _ => .sym 0)
  have agree : ∀ name, θ (labelCode name) = encode (applyBindings bindings (.fvar name)) :=
    fun name => labelCode_injective.extend_apply _ _ name
  exact ⟨schema, schemaMember, θ, inst_lower θ bindings _ _ origin.left (fun name _ => agree name),
    inst_lower θ bindings _ _ origin.right (fun name _ => agree name)⟩

/-- **A root rewrite of a source row is a source reduction, and its result is a source row.** -/
theorem rootStep_image (compiled : compile language = .ok schemas) {source : Pattern} {row : Expr}
    (stepped : RootStep schemas (encode source) row) :
    ∃ target, Step (engineBasePremises relEnv) language source target ∧ row = encode target := by
  obtain ⟨schema, schemaMember, θ, met, made⟩ := stepped
  obtain ⟨rule, member, origin⟩ := exists_rule (compile_origins compiled) schemaMember
  obtain ⟨bindings, bound⟩ := exists_bindings θ (freeVars rule.left) (captures θ _ _ source origin.left met)
  have left := inst_lower θ bindings _ _ origin.left bound
  have right := inst_lower θ bindings _ _ origin.right (fun name inRight => bound name (origin.bound name inRight))
  have sourceIs : applyBindings bindings rule.left = source := encode_injective (left.symm.trans met)
  refine ⟨applyBindings bindings rule.right, ?_, made.symm.trans right⟩
  rw [← sourceIs]
  exact step_of_instance (compile_plain compiled) member (matchCorrect_of_lower _ _ origin.left)
    (matchCorrect_of_lower _ _ origin.right) origin.bound bindings

/-- **The compiled schemas preserve and reflect the authored reduction.** -/
theorem rootStep_encode_iff (compiled : compile language = .ok schemas) (source target : Pattern) :
    RootStep schemas (encode source) (encode target) ↔
      Step (engineBasePremises relEnv) language source target := by
  refine ⟨fun stepped => ?_, rootStep_of_step compiled⟩
  obtain ⟨found, sourceStep, same⟩ := rootStep_image (relEnv := relEnv) compiled stepped
  rw [encode_injective same]
  exact sourceStep

/-! ## On the step -/

/-- The authored language under its own one-step reduction. -/
def sourceSystem (relEnv : RelationEnv) (language : LanguageDef) : GSLT :=
  equalityGSLT Pattern (Step (engineBasePremises relEnv) language)

/-- A source term is hosted by its row. -/
def EncodedAs (source : Pattern) (row : Expr) : Prop := row = encode source

/-- The authored language and root rewriting of its rows. -/
def encodedCorrespondence (relEnv : RelationEnv) (compiled : compile language = .ok schemas) :
    OperationalCorrespondence (sourceSystem relEnv language) (rootSystem schemas) where
  related := EncodedAs
  readStep := by
    intro source row next same stepped
    have isRow : row = encode source := same
    subst isRow
    obtain ⟨target, sourceStep, targetRow⟩ := rootStep_image (relEnv := relEnv) compiled stepped
    exact Or.inr ⟨target, sourceStep, targetRow⟩
  forward := by
    intro source target row same stepped
    have isRow : row = encode source := same
    subst isRow
    exact ⟨encode target, (executionPath_nonempty_iff_multiStep (rootSystem schemas) _ _).mpr
      (.step (rootStep_of_step compiled stepped) (.refl _)), rfl⟩

/-- **GSLT to transform.** An authored language of this fragment and the transform step
of its compiled program, in both directions. -/
def stepCorrespondence {O : Type} [DecidableEq O] [Infinite O] (relEnv : RelationEnv)
    (compiled : compile language = .ok schemas) :
    OperationalCorrespondence (sourceSystem relEnv language) (stepSystem O (rootRules schemas)) :=
  (encodedCorrespondence relEnv compiled).comp (rootCorrespondence (compile_closed compiled))

/-! ## The program as text -/

/-- A row in tcalc notation. -/
def rowText : Expr → String
  | .sym code => s!"s{code}"
  | .name code => s!"n{code}"
  | .app function argument => s!"(app {rowText function} {rowText argument})"
  | .code inner => s!"(code {rowText inner})"

/-- A row pattern in tcalc notation. -/
def termText : Tm → String
  | .var unknown => s!"$v{unknown}"
  | .const (.sym code) => s!"s{code}"
  | .const (.name code) => s!"n{code}"
  | .app .app arguments =>
      s!"(app {termText (arguments Presentation.Schematic.head)} {termText (arguments Presentation.Schematic.tail)})"
  | .app .code arguments => s!"(code {termText (arguments Presentation.Schematic.body)})"

/-- **The compiled program, started at one source term**: the one-firing step, the
row of the term, and one rule per schema. -/
def programText (schemas : List (Tm × Tm)) (source : Pattern) : String :=
  let rules := schemas.zipIdx.map fun (schema, index) =>
    s!"(rule r{index} (take {termText schema.1}) (make {termText schema.2}))"
  "\n".intercalate (["(step one)", rowText (encode source)] ++ rules) ++ "\n"

/-! ## Controls -/

namespace Controls

/-- `Choose(x, y) ~> x`. -/
def chooseFirst : RewriteRule where
  name := "choose-first"
  typeContext := [("x", .base "Term"), ("y", .base "Term")]
  premises := []
  left := .apply "Choose" [.fvar "x", .fvar "y"]
  right := .fvar "x"

/-- `Choose(x, y) ~> y`. -/
def chooseSecond : RewriteRule where
  name := "choose-second"
  typeContext := [("x", .base "Term"), ("y", .base "Term")]
  premises := []
  left := .apply "Choose" [.fvar "x", .fvar "y"]
  right := .fvar "y"

/-- A language with a genuine choice. -/
def choice : LanguageDef where
  name := "Choice"
  types := ["Term"]
  terms := [{ label := "Choose", category := "Term",
              params := [.simple "x" (.base "Term"), .simple "y" (.base "Term")], syntaxPattern := [] }]
  equations := []
  rewrites := [chooseFirst, chooseSecond]

theorem choice_compiles : ∃ schemas, compile choice = .ok schemas := by
  simp [compile, choice, chooseFirst, chooseSecond, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule,
    lower?, lowerList?, freeVars, ruleDepthAligned, depthAligned, captureDepth, captureDepthList]

/-- **Two successors, and no third.** -/
theorem choice_step_iff (first second target : Pattern) :
    Step (engineBasePremises relEnv) choice (.apply "Choose" [first, second]) target ↔
      target = first ∨ target = second := by
  obtain ⟨schemas, compiled⟩ := choice_compiles
  have plain := compile_plain compiled
  constructor
  · intro stepped
    obtain ⟨rule, member, bindings, sourceIs, targetIs⟩ := sides_of_step plain
      (fun rule member => by
        obtain ⟨schema, _, origin⟩ := exists_schema (compile_origins compiled) member
        exact matchCorrect_of_lower _ _ origin.left) stepped
    simp only [choice, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [chooseFirst, chooseSecond, applyBindings] at sourceIs targetIs ⊢ <;> simp_all
  · rintro (rfl | rfl)
    · simpa [chooseFirst, applyBindings] using
        step_of_instance (relEnv := relEnv) plain (rule := chooseFirst) (by simp [choice])
          (by simp [chooseFirst, isMatchCorrectAux, isMatchCorrectListAux]) (by simp [chooseFirst, isMatchCorrectAux])
          (by simp [chooseFirst, freeVars]) [("x", target), ("y", second)]
    · simpa [chooseSecond, applyBindings] using
        step_of_instance (relEnv := relEnv) plain (rule := chooseSecond) (by simp [choice])
          (by simp [chooseSecond, isMatchCorrectAux, isMatchCorrectListAux]) (by simp [chooseSecond, isMatchCorrectAux])
          (by simp [chooseSecond, freeVars]) [("x", first), ("y", target)]

/-- **Both successors are firings of the transform step, with different results.** -/
theorem choice_two_firings {O : Type} [DecidableEq O] [Infinite O] {schemas : List (Tm × Tm)}
    (compiled : compile choice = .ok schemas) {first second : Pattern} (different : first ≠ second)
    {s : SState O} (reads : ReadsBag s {encode (.apply "Choose" [first, second])}) :
    encode first ≠ encode second ∧
      ∀ target ∈ [first, second],
        ∃ (g : Firing O E {r | r ∈ rootRules schemas} s.frame)
          (admitted : (schematicStep O (rootRules schemas)).Admits (s := s) g),
          ReadsBag ((schematicStep O (rootRules schemas)).result g admitted) {encode target} := by
  refine ⟨fun same => different (encode_injective same), fun target member => ?_⟩
  exact firing_of_rootStep (compile_closed compiled) reads
    (rootStep_of_step (relEnv := RelationEnv.empty) compiled
      ((choice_step_iff first second target).mpr (by simpa using member)))

open Mettapedia.Languages.TransitionSystem in
/-- **An existing family of authored languages is covered**: every transition table compiles. -/
theorem table_compiles (table : Table) : ∃ schemas, compile table.language = .ok schemas := by
  have all : ∀ moves : List (String × String × String), ∃ schemas, lowerRules (moves.map moveRule) = .ok schemas := by
    intro moves
    induction moves with
    | nil => exact ⟨[], rfl⟩
    | cons move moves ih =>
        obtain ⟨schemas, others⟩ := ih
        simp [lowerRules, others, lowerRule, moveRule, state, lower?, lowerList?, freeVars, ruleDepthAligned,
          depthAligned, depthAlignedList]
  simpa [compile, Table.language, LanguageDef.hasAlgebraDeclarations, stateDeclaration] using all table.moves

/-- `A ~> y`, where nothing binds `y`. -/
def literalResult : RewriteRule where
  name := "literal-result"
  typeContext := [("y", .base "Term")]
  premises := []
  left := .apply "A" []
  right := .fvar "y"

/-- The language of that one rule. -/
def literal : LanguageDef where
  name := "LiteralResult"
  types := ["Term"]
  terms := [{ label := "A", category := "Term", params := [], syntaxPattern := [] }]
  equations := []
  rewrites := [literalResult]

theorem literal_refused : compile literal = .error (.unboundInResult "literal-result") := by
  simp [compile, literal, literalResult, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule, lower?,
    lowerList?, freeVars, ruleDepthAligned, depthAligned, captureDepth, captureDepthList]

theorem literal_plain : PlainRules literal := by
  intro rule member
  simp only [literal, List.mem_singleton] at member
  subst member
  simp [literalResult, ruleDepthAligned, depthAligned, captureDepth, captureDepthList]

/-- **A refused language keeps its ordinary execution**: `A` steps to the variable itself. -/
theorem literal_source_steps (target : Pattern) :
    Step (engineBasePremises relEnv) literal (.apply "A" []) target ↔ target = .fvar "y" := by
  rw [step_iff_exists_match literal_plain]
  simp [literal, literalResult, matchPattern, matchArgs, applyBindings, eq_comm]

/-- **Why it is refused.** Lowering the rule anyway would open `y` as an unknown, and
`A` would rewrite to every row, for example `A` itself, which is no source reduction. -/
theorem literal_naive_lowering_unsound :
    ∃ left right, lower? literalResult.left = some left ∧ lower? literalResult.right = some right ∧
      RootStep [(left, right)] (encode (.apply "A" [])) (encode (.apply "A" [])) ∧
      ¬ Step (engineBasePremises RelationEnv.empty) literal (.apply "A" []) (.apply "A" []) := by
  refine ⟨appTerm (symTerm 2) (appTerm (symTerm (labelCode "A")) (symTerm 0)), .var (labelCode "y"),
    by simp [literalResult, lower?, lowerList?], by simp [literalResult, lower?],
    ⟨_, List.mem_singleton_self _, fun _ => encode (.apply "A" []), by simp [encode, encodeList], rfl⟩, ?_⟩
  rw [literal_source_steps]
  simp

end Controls

#print axioms compile_origins
#print axioms rootStep_encode_iff
#print axioms stepCorrespondence
#print axioms Controls.choice_step_iff
#print axioms Controls.choice_two_firings
#print axioms Controls.table_compiles
#print axioms Controls.literal_naive_lowering_unsound

end Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
